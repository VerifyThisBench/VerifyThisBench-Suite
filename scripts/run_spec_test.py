"""
Spec-test driver for VerifyThisBench (the full benchmark, not the XS
relaxed version).

This script assumes the verification stage has already produced a results
directory — typically from running an LLM end-to-end on the full
benchmark — laid out as:

    <log-root>/<year>/<taskname>/<task_idx>/
        verification_<task_idx>_<attempt>.txt   (verifier result JSON)
        code_response_<task_idx>_<attempt>.txt  (the verified code)

For every task whose latest verification within the configured pass@K
window succeeded, the script:

  1. Loads the seed-test data from
     `<test-root>/<year>/<taskname>/seed_tests.json`.
  2. Asks the LLM to translate each seed test into an in-language
     `// test_case: <id>` assertion against the verified spec functions
     (`main_spec_pre` / `main_spec_post`), refining on compilation
     failure up to `--attempt` times.
  3. Re-runs the verifier on the augmented code.
  4. Optionally classifies the spec-test outcome with a second LLM call
     (turn off with `--skip-classify`).

Outputs are written next to the original verification artifacts:
    spectest_code_<task_idx>_<attempt>.txt           generated test code
    spectest_result_<task_idx>_<attempt>.txt         verifier JSON result
    spectest_classify_<task_idx>_<attempt>.txt       raw LLM classification
    spectest_classify_result_<task_idx>_<attempt>.json
                                                     parsed classification

Configuration:
  * The OpenAI client reads its base URL and API key from environment
    variables (`OPENAI_BASE_URL`, `OPENAI_API_KEY`).
  * Default model lives in `DEFAULT_MODEL` below; override with `--model`.
  * Resource paths: per-tool spec-test prompts are read from
    `spectest_prompts/<tool>.txt` (relative to the working directory).
"""

import argparse
import json
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

from openai import OpenAI


# ---------------------------------------------------------------------------
# LLM client + defaults
# ---------------------------------------------------------------------------

DEFAULT_MODEL = "openai/gpt-5.4"
MAX_VERIFICATION_ATTEMPT = 5

client = OpenAI(
    base_url=os.environ.get("OPENAI_BASE_URL", "https://openrouter.ai/api/v1"),
    api_key=os.environ.get("OPENAI_API_KEY", ""),
)


def chat_completion(messages, model=DEFAULT_MODEL, temperature=0.7):
    response = client.chat.completions.create(
        model=model,
        messages=messages,
        temperature=temperature,
    )
    return response.choices[0].message.content


def form_query_response(instruction, system_prompt, previous_context=None,
                        model=DEFAULT_MODEL):
    messages = [{"role": "system", "content": system_prompt}]
    if previous_context:
        messages.extend(previous_context)
    messages.append({"role": "user", "content": instruction})
    return chat_completion(messages, model)


def extract_code(response):
    if response is None:
        return None, None
    for tag in ["```code", "```dafny", "```whyml", "```c", "```java",
                "```cmbc", "```why3", "```rust", "```pvl", "```"]:
        start = response.find(tag)
        if start != -1:
            end = response.find("```", start + len(tag))
            if end != -1:
                return response[start + len(tag):end].strip(), tag[3:]
    return None, None


def save_to_file(path, *contents):
    with open(path, "w") as f:
        for content in contents:
            f.write(str(content))
            f.write("\n\n")


def _extract_json_block(text):
    """Pull the first ```json fenced block out of `text` and parse it."""
    if not isinstance(text, str):
        return None
    for tag in ("```json", "```JSON", "```"):
        s = text.find(tag)
        if s == -1:
            continue
        e = text.find("```", s + len(tag))
        if e == -1:
            continue
        body = text[s + len(tag):e].strip()
        try:
            return json.loads(body)
        except Exception:
            continue
    return None


# ---------------------------------------------------------------------------
# Verifier dispatch — uses the merged verify module
# ---------------------------------------------------------------------------

def eval_spec_test(tool, code_string, tag, timeout=60):
    """Run the verifier on the spec-test-augmented code.
    For verifast / vercors, the LLM-detected fence tag is used as the
    file extension so the verifier picks the correct frontend."""
    if tool == "dafny":
        from verify import eval_dafny_spec
        return eval_dafny_spec(code_string, timeout)
    if tool == "framac":
        from verify import eval_framac_spec
        return eval_framac_spec(code_string, timeout)
    if tool == "vercors":
        from verify import eval_vercors
        return eval_vercors(code_string, timeout, tag or "pvl")
    if tool == "verifast":
        from verify import eval_verifast
        return eval_verifast(code_string, timeout, tag or "c")
    if tool == "verus":
        from verify import eval_verus
        return eval_verus(code_string, timeout)
    if tool == "why3":
        from verify import eval_why3
        return eval_why3(code_string, timeout)
    if tool == "cbmc":
        from verify import eval_cbmc
        return eval_cbmc(code_string, timeout)
    return {"error": f"No spec-test eval for tool: {tool}", "returncode": -1}


# ---------------------------------------------------------------------------
# Spec-test generation prompt + refinement loop
# ---------------------------------------------------------------------------

def _load_spec_test_prompt(tool: str) -> str:
    prompt_file = f"spectest_prompts/{tool}.txt"
    if os.path.exists(prompt_file):
        with open(prompt_file) as f:
            return f.read()
    return "Add test case assertions to validate the specifications."


_SPEC_TEST_CORE_WORKFLOW = """

CORE WORKFLOW:
The implementation already exposes its specification through a standard ABI:
- `main_spec_pre(...)` — the precondition (returns bool or equivalent)
- `main_spec_post(...)` — the postcondition (returns bool or equivalent)

Your job is simple: for each seed test case, construct the input values and call the existing spec functions directly, then assert against the expected result.

For each seed test case:
- If condition is "pre" and expected is true:   `assert(main_spec_pre(test_values))`
- If condition is "pre" and expected is false:  `assert(!main_spec_pre(test_values))`
- If condition is "post" and expected is true:  `assert(main_spec_post(test_values, result_value))`
- If condition is "post" and expected is false: `assert(!main_spec_post(test_values, result_value))`

ASSERTION TAGGING (required for downstream parsing):
- Every assertion line MUST end with a trailing comment containing the seed
  test case's `id`, in the exact form:  `// test_case: <id>`
  (use the single-line comment syntax appropriate for the target language —
  `//` for C / Java / Rust / Dafny, `(*  *)` for Why3 / OCaml-style, etc.)
- One assertion per line so the comment unambiguously identifies which case
  it covers.
- If a test function contains multiple assertions, tag each one with its own
  `// test_case: <id>` comment.

RULES:
- Do NOT modify the original implementation or the spec functions in any way.
- Do NOT redefine or duplicate `main_spec_pre` or `main_spec_post`.
- The ONLY thing you add is: test functions that construct inputs, call the
  existing spec functions, and assert.
- Each seed test case becomes its own test function, named by its test ID.
- All test functions are called from a main/entry function.
"""


def run_spec_test(tool, original_code, seed_tests, time_limit,
                  description=None, task_content=None, max_attempts=5,
                  log_dir=None, task_idx=None, main_attempt=None,
                  model=DEFAULT_MODEL):
    """Generate seed-test assertions against the verified spec, run the
    verifier on the augmented code, and refine on compilation failure up
    to `max_attempts` times. Returns (test_code, test_result)."""
    if not seed_tests:
        return None, "No seed tests found"

    spectest_prompt = _load_spec_test_prompt(tool)
    spectest_prompt += _SPEC_TEST_CORE_WORKFLOW

    context_parts = []
    if description:
        context_parts.append(f"Challenge description:\n{description}")
    if task_content:
        context_parts.append(f"Task requirement:\n{task_content}")
    context_parts.append(f"Original verified implementation:\n{original_code}")
    context_parts.append(
        f"Seed test data:\n{json.dumps(seed_tests, indent=2)}")

    test_instruction = (
        "The code already has `main_spec_pre` and `main_spec_post` spec "
        "functions exposed. Generate test functions that plug in the seed "
        "test case values and assert against expected results.\n\n"
        + "\n".join(context_parts)
        + "\n\nFor each seed test case, create a test function that:\n"
        "1. Constructs the input values from the test case\n"
        "2. Calls `main_spec_pre(...)` or `main_spec_post(...)` depending "
        "on the \"condition\" field\n"
        "3. Asserts the result matches the \"expected\" boolean"
    )

    spec_test_context = []
    error_feedback_inst = (
        "Here is the error from the spec test verification. Fix the test "
        "case issues without modifying the original implementation:\n"
    )

    for attempt in range(1, max_attempts + 1):
        print(f"  Spec-test attempt {attempt}")
        test_response = form_query_response(
            test_instruction, spectest_prompt, spec_test_context, model=model,
        )
        test_code, tag = extract_code(test_response)

        if not test_code:
            return None, "No test code generated"

        if log_dir and task_idx is not None and main_attempt is not None:
            save_to_file(
                os.path.join(
                    log_dir,
                    f"spectest_code_{task_idx}_{main_attempt}_sub{attempt}.txt"),
                test_code,
            )

        test_result = eval_spec_test(tool, test_code, tag, time_limit)

        if log_dir and task_idx is not None and main_attempt is not None:
            save_to_file(
                os.path.join(
                    log_dir,
                    f"spectest_result_{task_idx}_{main_attempt}_sub{attempt}.txt"),
                json.dumps(test_result, indent=2),
            )

        if test_result.get("succeed") and not test_result.get("partial"):
            print(f"  Spec-test passed on attempt {attempt}")
            return test_code, test_result

        # Only refine on compilation errors; verification failures are signals
        # that the generated tests caught a real spec gap.
        if not test_result.get("compilation_err"):
            print(f"  Spec-test verification failure (non-compilation) on "
                  f"attempt {attempt} - returning result")
            return test_code, test_result

        if attempt == max_attempts:
            print(f"  Spec-test failed to compile after {max_attempts} attempts")
            return test_code, test_result

        error_msg = test_result.get("out", "") + test_result.get("err", "")
        if test_result.get("timed_out", False):
            error_msg = "Spec test execution timed out."

        spec_test_context.extend([
            {"role": "user", "content": test_instruction},
            {"role": "assistant", "content": test_response},
        ])
        test_instruction = error_feedback_inst + error_msg
        print(f"  Compilation error - refining spec test "
              f"(attempt {attempt + 1})")

    return None, "Max spec test attempts reached (compilation errors)"


# ---------------------------------------------------------------------------
# Eligible-task discovery
# ---------------------------------------------------------------------------

# Filenames look like `verification_<task_idx>_<attempt>.txt` where task_idx
# is purely digits.
_VERIF_RE = re.compile(r"^verification_(\d+)_(\d+)\.txt$")


def find_eligible_tasks(log_root, year_filter=None, task_filter=None):
    """Yield one record per task whose latest verification attempt within
    1..MAX_VERIFICATION_ATTEMPT is a clean success."""
    by_task = {}
    for year in sorted(os.listdir(log_root)):
        if year_filter and year not in year_filter:
            continue
        ydir = os.path.join(log_root, year)
        if not os.path.isdir(ydir):
            continue
        for taskname in sorted(os.listdir(ydir)):
            if task_filter and taskname not in task_filter:
                continue
            tdir = os.path.join(ydir, taskname)
            if not os.path.isdir(tdir):
                continue
            for ti_name in sorted(os.listdir(tdir)):
                ti_dir = os.path.join(tdir, ti_name)
                if not os.path.isdir(ti_dir):
                    continue
                try:
                    task_idx = int(ti_name)
                except ValueError:
                    continue
                for fn in os.listdir(ti_dir):
                    m = _VERIF_RE.match(fn)
                    if not m:
                        continue
                    if int(m.group(1)) != task_idx:
                        continue
                    attempt = int(m.group(2))
                    if attempt > MAX_VERIFICATION_ATTEMPT:
                        continue
                    by_task.setdefault((year, taskname, task_idx),
                                       {})[attempt] = ti_dir

    for (year, taskname, task_idx), attempts_map in by_task.items():
        last_attempt = max(attempts_map.keys())
        ti_dir = attempts_map[last_attempt]
        verif_path = os.path.join(
            ti_dir, f"verification_{task_idx}_{last_attempt}.txt")
        try:
            with open(verif_path) as f:
                verif = json.load(f)
        except Exception:
            continue
        if not (isinstance(verif, dict) and verif.get("succeed")
                and not verif.get("partial")):
            continue

        code_path = os.path.join(
            ti_dir, f"code_response_{task_idx}_{last_attempt}.txt")
        if not os.path.exists(code_path):
            continue
        with open(code_path) as f:
            code = f.read().strip()
        if not code or code == "NO CODE FOUND":
            continue

        yield {
            "year": year,
            "taskname": taskname,
            "task_idx": task_idx,
            "attempt": last_attempt,
            "log_dir": ti_dir,
            "code": code,
        }


# ---------------------------------------------------------------------------
# Side data
# ---------------------------------------------------------------------------

def load_dataset_index(dataset_path):
    """Returns (desc_by_ch, tasks_by_ch) — keyed by (year, taskname)."""
    with open(dataset_path) as f:
        d = json.load(f)
    desc_by_ch = {}
    tasks_by_ch = {}
    for c in d.get("challenges", []):
        key = (str(c.get("year", "")), c.get("name", ""))
        desc_by_ch[key] = c.get("description", "") or ""
        tasks_by_ch[key] = c.get("tasks", []) or []
    return desc_by_ch, tasks_by_ch


def load_seed_tests(test_root, year, taskname):
    p = os.path.join(test_root, year, taskname, "seed_tests.json")
    if os.path.exists(p):
        with open(p) as f:
            return json.load(f)
    return None


def filter_seeds_for_task(seeds_obj, task_idx):
    """Return a copy of `seeds_obj` whose `seed_tests` list keeps only seeds
    whose `task` field is `task1`..`task<task_idx>` — the cumulative slice
    of in-scope seeds for the current task. Seeds with a missing or
    unparseable `task` field are dropped."""
    if not isinstance(seeds_obj, dict):
        return seeds_obj
    kept = []
    for t in seeds_obj.get("seed_tests", []) or []:
        m = re.match(r"task(\d+)", str(t.get("task", "")))
        if m and int(m.group(1)) <= task_idx:
            kept.append(t)
    out = {k: v for k, v in seeds_obj.items() if k != "seed_tests"}
    out["seed_tests"] = kept
    return out


# ---------------------------------------------------------------------------
# Classification prompt + post-spec-test classifier
# ---------------------------------------------------------------------------

_CLASSIFY_PROMPT = """\
You are an expert in formal verification. The implementation below has
been verified as correct against its original requirements by the {tool}
formal-verification tool. We then generated seed-based spec-test
assertions (each tagged with `// test_case: <id>`) and re-ran the
verifier. Some assertions may have been discharged (passed) and others
may not (failed). Your job is to inspect the run and produce two
outputs:

SCOPE — IMPORTANT.
    The IMPLEMENTATION + SPEC TESTS section may contain extra `//
    test_case: <id>` assertions that lie OUTSIDE the current task's
    scope (for example, assertions belonging to tasks that come after
    the current one in the same challenge, left over from earlier
    pipeline stages). The SEED TEST DATA section below lists ONLY the
    in-scope seeds for the CURRENT task. Treat that list as the source
    of truth.

    Rules:
      * Every entry you put in `test_cases` MUST have a `test_id` that
        appears in the SEED TEST DATA. Do NOT fabricate test_ids and do
        NOT classify out-of-scope assertions.
      * If the verifier log records pass/fail outcomes for out-of-scope
        assertions, ignore them. They are not evidence about the
        current task's spec.
      * The overall verdict (B) must be based ONLY on in-scope seeds.

(A) Per-test-case classification.

    For each seed test case, decide whether the verifier discharged its
    assertion (verdict = "pass") or not (verdict = "fail"), then assign
    a category from the appropriate set:

    PASS categories (for assertions the verifier discharged):
    - truly_correct       — the assertion corresponds to what the seed
                            wanted, the spec captures the intended
                            property, and the verifier discharged it.
    - test_translation_problem — the translator made a mistake on a seed
                            that the spec CAN faithfully express.
    - spec_gap            — no faithful translation exists against the
                            current spec.

    FAIL categories (for assertions the verifier rejected):
    - test_translation_problem — same definition; the failing assertion
                            could have been correctly translated.
    - spec_bug            — the pre/postcondition is wrong or
                            incomplete for the intended behavior.
    - automation_limitation — the spec is correct and the assertion is
                            semantically true, but the verifier cannot
                            discharge it without proof hints.

(B) Overall spec evaluation.

    Choose ONE verdict for the spec as a whole:
    - correct       — all passing cases are truly_correct (with
                      automation/translator noise tolerated on the fail
                      side); no spec_gap on properties the task cares
                      about.
    - minor_issues  — the main property is captured but isolated
                      weaknesses exist (translator errors or auxiliary
                      gaps).
    - major_issues  — the spec does NOT match the task. Triggered by
                      any failing case being a spec_bug, OR a passing
                      case being spec_gap on a load-bearing property.

Output format — emit a SINGLE ```json``` fenced block:

```json
{{
  "overall_evaluation": "correct" | "minor_issues" | "major_issues",
  "overall_reasoning": "<one or two sentences justifying the verdict>",
  "test_cases": [
    {{
      "test_id": "<id from the seed>",
      "verdict": "pass" | "fail",
      "category": "<see lists above>",
      "reasoning": "<one or two sentences citing specific lines / values / verifier output>"
    }}
  ]
}}
```

------------------------ TASK DESCRIPTION ------------------------
{description}

------------------------ TASK REQUIREMENT ------------------------
{task_content}

----------------- IMPLEMENTATION + SPEC TESTS --------------------
{test_code}

------------------------ SEED TEST DATA --------------------------
{seed_tests_json}

----------------- VERIFIER LOG (last attempt) --------------------
{verifier_log}
"""


def _classify_after_spectest(task, *, tool, model, test_code, test_result,
                             seed_tests, description, task_content):
    label = (f"{task['year']}/{task['taskname']}/task{task['task_idx']}"
             f"@{task['attempt']}")
    if not test_code:
        print(f"[classify-skip] {label}  (no test_code)")
        return

    if isinstance(test_result, dict):
        succeed = bool(test_result.get("succeed"))
        partial = bool(test_result.get("partial"))
        verifier_log = json.dumps(test_result, indent=2)
    else:
        succeed = False
        partial = False
        verifier_log = str(test_result)

    if succeed and not partial:
        spec_status = "PASS"
    elif partial:
        spec_status = "PARTIAL"
    else:
        spec_status = "FAIL"

    prompt = _CLASSIFY_PROMPT.format(
        tool=tool,
        description=description or "(no description provided)",
        task_content=task_content or "(no per-task content provided)",
        test_code=test_code,
        seed_tests_json=json.dumps(seed_tests, indent=2),
        verifier_log=verifier_log,
    )

    print(f"[classify {spec_status}] {label}")
    sys.stdout.flush()
    start = time.time()
    try:
        response = chat_completion(
            [{"role": "user", "content": prompt}], model=model)
    except Exception as exc:
        print(f"[classify ERROR] {label}: {exc!r}")
        return
    elapsed = time.time() - start
    print(f"[classify done] {label}  ({elapsed:.2f}s)")

    raw_path = os.path.join(
        task["log_dir"],
        f"spectest_classify_{task['task_idx']}_{task['attempt']}.txt")
    save_to_file(raw_path, response or "")

    parsed = _extract_json_block(response)
    if parsed is not None:
        parsed_path = os.path.join(
            task["log_dir"],
            f"spectest_classify_result_{task['task_idx']}_{task['attempt']}.json")
        envelope = {"spec_test_status": spec_status.lower()}
        if isinstance(parsed, dict):
            envelope.update(parsed)
        else:
            envelope["test_cases"] = parsed
        with open(parsed_path, "w") as f:
            json.dump(envelope, f, indent=2)


# ---------------------------------------------------------------------------
# Per-task driver
# ---------------------------------------------------------------------------

def _process(task, *, tool, time_limit, spectest_attempts, model,
             desc_by_ch, tasks_by_ch, test_root,
             skip_classify, force_test, force_classify):
    label = (f"{task['year']}/{task['taskname']}/task{task['task_idx']}"
             f"@{task['attempt']}")

    spectest_code_path = os.path.join(
        task["log_dir"],
        f"spectest_code_{task['task_idx']}_{task['attempt']}.txt")
    spectest_result_path = os.path.join(
        task["log_dir"],
        f"spectest_result_{task['task_idx']}_{task['attempt']}.txt")
    classify_raw_path = os.path.join(
        task["log_dir"],
        f"spectest_classify_{task['task_idx']}_{task['attempt']}.txt")
    classify_json_path = os.path.join(
        task["log_dir"],
        f"spectest_classify_result_{task['task_idx']}_{task['attempt']}.json")

    has_spectest = os.path.exists(spectest_result_path)
    has_classify = (os.path.exists(classify_raw_path)
                    or os.path.exists(classify_json_path))

    classify_needed = not skip_classify
    if (has_spectest and (has_classify or skip_classify)
            and not force_test and not force_classify):
        print(f"[skip-existing] {label}")
        return

    key = (task["year"], task["taskname"])
    description = desc_by_ch.get(key, "")
    tasks_list = tasks_by_ch.get(key, [])
    task_content = ""
    if 1 <= task["task_idx"] <= len(tasks_list):
        task_content = tasks_list[task["task_idx"] - 1].get("content", "") or ""

    seed_tests = load_seed_tests(test_root, task["year"], task["taskname"])
    if seed_tests is not None:
        # Restrict the seed list to the cumulative scope of the current task
        # (seeds for task1..task<task_idx>). Seeds belonging to later tasks
        # in the same challenge are filtered out so the spec-test generator
        # — and the downstream classifier — only see in-scope cases.
        seed_tests = filter_seeds_for_task(seed_tests, task["task_idx"])

    # ---- Spec-test stage ----
    if has_spectest and not force_test:
        try:
            with open(spectest_result_path) as f:
                test_result = json.load(f)
        except Exception as exc:
            print(f"[reuse-fail] {label}: {exc!r}")
            return
        test_code = None
        if os.path.exists(spectest_code_path):
            with open(spectest_code_path) as f:
                test_code = f.read().strip()

        if (isinstance(test_result, dict) and "error" in test_result
                and "succeed" not in test_result):
            print(f"[reuse-skip] {label}  (error stub: "
                  f"{test_result.get('error')})")
            return
        print(f"[reuse] {label}  (loaded existing spectest artifacts)")
    else:
        if not seed_tests:
            print(f"[no-seed]  {label}  (no seed_tests.json under {test_root})")
            save_to_file(spectest_result_path,
                         json.dumps({"error": "no_seed_tests"}, indent=2))
            return

        print(f"\n[run] {label}  (max_attempts={spectest_attempts}, "
              f"model={model})")
        start = time.time()
        test_code, test_result = run_spec_test(
            tool=tool,
            original_code=task["code"],
            seed_tests=seed_tests,
            time_limit=time_limit,
            description=description,
            task_content=task_content,
            max_attempts=spectest_attempts,
            log_dir=task["log_dir"],
            task_idx=task["task_idx"],
            main_attempt=task["attempt"],
            model=model,
        )
        elapsed = time.time() - start

        if test_code:
            save_to_file(spectest_code_path, test_code)
        if isinstance(test_result, dict):
            save_to_file(spectest_result_path,
                         json.dumps(test_result, indent=2))
            succeeded = bool(test_result.get("succeed"))
            was_partial = bool(test_result.get("partial"))
            if succeeded and not was_partial:
                status = "PASS"
            elif was_partial:
                status = "PARTIAL"
            else:
                status = "FAIL"
        else:
            save_to_file(spectest_result_path,
                         json.dumps({"error": str(test_result)}, indent=2))
            status = "ERROR"
        print(f"[done {status}] {label}  ({elapsed:.1f}s)")

    # ---- Classification stage ----
    if skip_classify:
        return
    if has_classify and not force_classify:
        print(f"[classify-skip] {label}  (classification on disk)")
        return

    _classify_after_spectest(
        task, tool=tool, model=model,
        test_code=test_code, test_result=test_result,
        seed_tests=seed_tests,
        description=description, task_content=task_content,
    )


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tool", type=str, required=True,
                        help="Verifier the existing logs were generated with "
                             "(dafny / why3 / verus / framac / verifast / "
                             "vercors / cbmc).")
    parser.add_argument("--log-root", type=str, required=True,
                        help="Existing per-tool results dir.")
    parser.add_argument("--attempt", type=int, default=5,
                        help="Max refinement attempts for spec-test "
                             "generation (default: 5).")
    parser.add_argument("--timelimit", type=int, default=600,
                        help="Per-invocation tool time limit (default: 600s).")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL,
                        help=f"LLM used for spec-test generation and "
                             f"classification (default: {DEFAULT_MODEL}).")
    parser.add_argument("--year", action="append", default=None,
                        help="Restrict to year(s) (repeatable).")
    parser.add_argument("--task-filter", action="append", default=None,
                        help="Restrict to challenge name(s) (repeatable).")
    parser.add_argument("--workers", type=int, default=1,
                        help="Parallel worker count (default: 1).")
    parser.add_argument("--dataset", type=str,
                        default="../VerifyThisBenchDS/dataset.json",
                        help="Path to VerifyThisBenchDS/dataset.json.")
    parser.add_argument("--test-root", type=str,
                        default="../VerifyThisBenchTest/all",
                        help="Seed-test root containing "
                             "<year>/<taskname>/seed_tests.json.")
    parser.add_argument("--skip-classify", action="store_true",
                        help="Generate + run spec tests only; skip the "
                             "second-stage LLM classification.")
    parser.add_argument("--force-test", action="store_true",
                        help="Re-run spec test even if existing artifacts "
                             "are on disk.")
    parser.add_argument("--force-classify", action="store_true",
                        help="Re-run classification even if existing.")
    parser.add_argument("--force", action="store_true",
                        help="Convenience flag: implies --force-test AND "
                             "--force-classify.")
    args = parser.parse_args()

    force_test = args.force_test or args.force
    force_classify = args.force_classify or args.force

    if not os.path.isdir(args.log_root):
        sys.exit(f"--log-root not found: {args.log_root}")
    if not os.path.isdir(args.test_root):
        sys.exit(f"--test-root not found: {args.test_root}")
    if not os.path.isfile(args.dataset):
        sys.exit(f"--dataset not found: {args.dataset}")

    year_filter = set(args.year) if args.year else None
    task_filter = set(args.task_filter) if args.task_filter else None
    desc_by_ch, tasks_by_ch = load_dataset_index(args.dataset)

    print(f"Tool:         {args.tool}")
    print(f"Log root:     {args.log_root}")
    print(f"Test root:    {args.test_root}")
    print(f"Model:        {args.model}")
    print(f"Max attempts: {args.attempt}")
    print(f"Time limit:   {args.timelimit}s")
    print(f"Skip classify:{args.skip_classify}")
    if year_filter:
        print(f"Years:        {sorted(year_filter)}")
    if task_filter:
        print(f"Tasks:        {sorted(task_filter)}")

    eligible = sorted(
        find_eligible_tasks(args.log_root, year_filter, task_filter),
        key=lambda t: (t["year"], t["taskname"], t["task_idx"]),
    )
    print(f"Eligible tasks: {len(eligible)}")
    if not eligible:
        return

    workers = max(1, args.workers)
    print(f"Workers: {workers}")

    if workers == 1:
        for i, t in enumerate(eligible, 1):
            print(f"\n=== [{i}/{len(eligible)}] ===")
            _process(t, tool=args.tool, time_limit=args.timelimit,
                     spectest_attempts=args.attempt, model=args.model,
                     desc_by_ch=desc_by_ch, tasks_by_ch=tasks_by_ch,
                     test_root=args.test_root,
                     skip_classify=args.skip_classify,
                     force_test=force_test, force_classify=force_classify)
        return

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {
            pool.submit(
                _process, t,
                tool=args.tool, time_limit=args.timelimit,
                spectest_attempts=args.attempt, model=args.model,
                desc_by_ch=desc_by_ch, tasks_by_ch=tasks_by_ch,
                test_root=args.test_root,
                skip_classify=args.skip_classify,
                force_test=force_test, force_classify=force_classify,
            ): t for t in eligible
        }
        done = 0
        for fut in as_completed(futures):
            done += 1
            t = futures[fut]
            label = f"{t['year']}/{t['taskname']}/task{t['task_idx']}"
            try:
                fut.result()
                print(f"[{done}/{len(eligible)}] OK   {label}")
            except Exception as exc:
                print(f"[{done}/{len(eligible)}] FAIL {label} - {exc!r}")


if __name__ == "__main__":
    main()
