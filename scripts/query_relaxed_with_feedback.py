"""
Feedback-driven driver for VerifyThisBenchXS.

Workflow (per template):
  1. Read a template solution (with TODO holes for spec / impl / inv) from
     `../VerifyThisBenchXS/dataset.json`.
  2. Ask the LLM to fill in the TODOs.
  3. Run the formal verifier on the result.
  4. On verification failure, feed the error log back to the LLM and retry,
     up to `--attempt` total tries.

Configuration:
  * The OpenAI client reads its base URL and API key from environment
    variables. Set `OPENAI_BASE_URL` and `OPENAI_API_KEY` (or the
    OpenRouter equivalents) before running.
  * The default model is set in `DEFAULT_MODEL` below; override per-run
    with `--model`.
  * The output log root is set in `DEFAULT_LOG_ROOT` below; override per-
    run with `--log-root`.
  * Resource paths: prompts are read from `../prompts/coherent_prompt.txt`
    and `../prompts/system_prompts/<tool>.txt`. Adjust these paths if your
    layout differs.
"""

import argparse
import json
import os
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

from openai import OpenAI


# ---------------------------------------------------------------------------
# LLM client + defaults
# ---------------------------------------------------------------------------

DEFAULT_MODEL = "openai/gpt-5.4"
DEFAULT_LOG_ROOT = "../results"
PROMPTS_DIR = "../prompts"


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
    """Pull the first fenced code block. Returns (body, fence-tag-without-backticks)."""
    if response is None:
        return None, None
    for tag in ["```code", "```dafny", "```c", "```whyml", "```java",
                "```cmbc", "```why3", "```rust", "```pvl", "```"]:
        start = response.find(tag)
        if start != -1:
            end = response.find("```", start + len(tag))
            if end != -1:
                return response[start + len(tag):end].strip(), tag[3:]
    return None, None


def extract_coherence(response):
    """Pull the `/answer{yes|no}` token from a coherence-check response."""
    if response is None:
        return None
    start = response.find("/answer{")
    end = response.find("}", start)
    if start != -1 and end != -1:
        return response[start + len("/answer{"):end].strip()
    return None


def save_to_file(path, *contents):
    with open(path, "w") as f:
        for content in contents:
            f.write(str(content))
            f.write("\n\n")


# ---------------------------------------------------------------------------
# Dataset loading (VerifyThisBenchXS)
# ---------------------------------------------------------------------------

# Subchallenge `type` field → CLI --task-kind label.
_XS_TYPE_TO_TASK_KIND = {
    "specification": "spec-gen",
    "implementation": "impl-gen",
    "loop-invariant": "inv-gen",
}


def matches_task_kind_xs(sub_type: str, task_kind: str) -> bool:
    if task_kind == "all":
        return True
    mapped = _XS_TYPE_TO_TASK_KIND.get(sub_type)
    if mapped is None:
        raise ValueError(
            f"Unknown VerifyThisBenchXS subchallenge type {sub_type!r}; "
            f"expected one of {sorted(_XS_TYPE_TO_TASK_KIND)}"
        )
    return mapped == task_kind


def load_xs_dataset(dataset_path: str) -> list:
    with open(dataset_path, "r", encoding="utf-8") as f:
        payload = json.load(f)
    return payload.get("challenges", [])


def iter_xs_templates(challenges, tool_filter=None, task_kind="all"):
    """Flatten the nested VerifyThisBenchXS structure into template records."""
    for challenge in challenges:
        year = str(challenge.get("year", ""))
        taskname = challenge.get("name", "")
        tools = challenge.get("tools", {}) or {}
        for tool, tool_entry in tools.items():
            if tool_filter and tool.lower() != tool_filter:
                continue
            description = (tool_entry or {}).get("description", "") or ""
            for sub in (tool_entry or {}).get("challenges", []) or []:
                sub_type = sub.get("type", "") or ""
                if not matches_task_kind_xs(sub_type, task_kind):
                    continue

                sub_id = sub.get("id", "")
                splits = sub.get("splits", []) or []

                def _record(split_id, code):
                    if code is None:
                        return None
                    return {
                        "year": year,
                        "taskname": taskname,
                        "tool": tool,
                        "description": description,
                        "challenge_id": sub_id,
                        "challenge_type": sub_type,
                        "split_id": split_id,
                        "code": code,
                    }

                base_rec = _record(sub_id, sub.get("code"))
                if base_rec is not None:
                    yield base_rec
                for split in splits:
                    rec = _record(split.get("id", ""), split.get("code"))
                    if rec is not None:
                        yield rec


# ---------------------------------------------------------------------------
# Verification dispatch
# ---------------------------------------------------------------------------

def eval_code(tool, code_string, tag, timeout=60):
    if tool == "verus":
        from verify import eval_verus
        return eval_verus(code_string, timeout)
    if tool == "why3":
        from verify import eval_why3
        return eval_why3(code_string, timeout)
    if tool == "dafny":
        from verify import eval_dafny
        return eval_dafny(code_string, timeout)
    if tool == "framac":
        from verify import eval_framac
        return eval_framac(code_string, timeout)
    if tool == "verifast":
        from verify import eval_verifast
        return eval_verifast(code_string, timeout, tag)
    if tool == "vercors":
        from verify import eval_vercors
        return eval_vercors(code_string, timeout, tag)
    if tool == "cbmc":
        from verify import eval_cbmc
        return eval_cbmc(code_string, timeout)
    return {"error": f"No eval implementation for tool: {tool}",
            "returncode": -1}


# ---------------------------------------------------------------------------
# Per-template worker
# ---------------------------------------------------------------------------

def _process_template(
    tpl,
    index,
    total,
    *,
    attempt_limit,
    time_limit,
    log_root,
    coherent_prompt,
    fill_todo_inst,
    error_feedback_inst,
    get_system_prompt,
    model,
):
    year = tpl["year"]
    taskname = tpl["taskname"]
    tool = tpl["tool"]
    description = tpl["description"]
    filename = tpl["split_id"]
    template_solution = tpl["code"]

    system_prompt = get_system_prompt(tool)
    label = f"{year}/{taskname}/{tool}/{filename}"
    print(f"\n[{index}/{total}] Processing {label}")

    task_context = [
        {
            "role": "user",
            "content": (
                "Target this verification problem; plan out your steps and "
                "write your final answer:\n\n"
                f"{description}. Your task is to complete a given template "
                "solution and fill in the TODO fields"
            ),
        },
        {"role": "assistant", "content": "OK, I'm ready to help."},
    ]

    attempt = 1
    error = None
    starttime = time.time()
    refine_context = task_context.copy()

    while attempt <= attempt_limit:
        start = time.time()
        query_inst = (
            fill_todo_inst + template_solution
            if attempt == 1
            else error_feedback_inst + f"{error}"
        )

        response = form_query_response(
            query_inst, system_prompt, task_context, model=model)
        code_response, tag = extract_code(response)
        print(f"[{index}/{total}] Attempt {attempt} code response: "
              f"{time.time() - start:.2f}s ({label})")

        log_dir = os.path.join(log_root, year, taskname, tool, str(attempt))
        os.makedirs(log_dir, exist_ok=True)

        code_path = os.path.join(
            log_dir, f"code_response_{filename}_{attempt}.txt")
        save_to_file(code_path, code_response or "NO CODE FOUND")

        refine_context.extend([
            {"role": "user", "content": query_inst},
            {"role": "assistant", "content": response},
        ])
        context_path = os.path.join(
            log_dir, f"refine_context_{filename}_{attempt}.txt")
        save_to_file(context_path, json.dumps(refine_context, indent=4))

        coherence_check = form_query_response(
            coherent_prompt,
            system_prompt,
            task_context + [
                {"role": "user", "content": fill_todo_inst + template_solution},
                {"role": "assistant", "content": response},
            ],
            model=model,
        )
        coherence_response = extract_coherence(coherence_check)
        correctness_path = os.path.join(
            log_dir, f"coherence_check_{filename}_{attempt}.txt")
        save_to_file(correctness_path, coherence_check,
                     coherence_response or "NO COHERENCE FOUND")

        verification_path = os.path.join(
            log_dir, f"verification_{filename}_{attempt}.txt")
        if not code_response:
            attempt += 1
            error = "Your previous attempt did not contain any code."
            save_to_file(verification_path, json.dumps("NO CODE FOUND"))
            continue

        print(f"[{index}/{total}] Verifying {label} (attempt {attempt})")
        start = time.time()
        result = eval_code(tool, code_response, tag, time_limit)
        print(f"[{index}/{total}] Evaluation takes {time.time() - start:.2f}s "
              f"({label})")
        save_to_file(verification_path, json.dumps(result, indent=2))
        error = result["out"] + result["err"] if not result["timed_out"] \
                else "Execution timed out."

        if result["succeed"] and not result["partial"]:
            break
        attempt += 1

    print(f"[{index}/{total}] Task completed in {time.time() - starttime:.2f}s "
          f"({label})")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tool", type=str, default=None,
                        help="Optional verification tool filter (e.g. why3).")
    parser.add_argument("--attempt", type=int, required=True,
                        help="Maximum attempts per template.")
    parser.add_argument("--timelimit", type=int, required=True,
                        help="Time limit for the verifier in seconds.")
    parser.add_argument(
        "--task-kind",
        choices=["all", "spec-gen", "impl-gen", "inv-gen"],
        default="all",
        help="Which VerifyThisBenchXS task type to run.",
    )
    parser.add_argument(
        "--dataset",
        type=str,
        default="../VerifyThisBenchXS/dataset.json",
        help="Path to VerifyThisBenchXS/dataset.json.",
    )
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL,
                        help=f"LLM model name (default: {DEFAULT_MODEL}).")
    parser.add_argument("--log-root", type=str, default=DEFAULT_LOG_ROOT,
                        help=f"Output log root (default: {DEFAULT_LOG_ROOT}).")
    parser.add_argument(
        "--workers", type=int, default=1,
        help="Number of templates to process in parallel (default: 1).",
    )
    args = parser.parse_args()

    tool_filter = args.tool.lower() if args.tool else None
    attempt_limit = args.attempt
    time_limit = args.timelimit
    task_kind = args.task_kind

    coherent_prompt_file = os.path.join(PROMPTS_DIR, "coherent_prompt.txt")
    with open(coherent_prompt_file, "r") as f:
        coherent_prompt = f.read()

    print(f"Loading dataset:    {args.dataset}")
    print(f"Saving logs under:  {args.log_root}")
    print(f"Model:              {args.model}")
    if tool_filter:
        print(f"Filtering tool:    {tool_filter}")
    print(f"Task kind:          {task_kind}")

    challenges = load_xs_dataset(args.dataset)
    templates = list(iter_xs_templates(
        challenges, tool_filter=tool_filter, task_kind=task_kind,
    ))
    templates.sort(
        key=lambda t: (t["year"], t["taskname"], t["tool"], t["split_id"]))
    print(f"Loaded {len(templates)} template(s) to process")

    fill_todo_inst = (
        "Complete the TODO fields in the solution template. "
        "Fix any potential syntax error as necessary.\n"
    )
    error_feedback_inst = "Here is the error log. Fix the issues.\n"

    # Cache system prompts per tool (shared across workers).
    system_prompt_cache = {}
    system_prompt_lock = threading.Lock()

    def get_system_prompt(tool):
        with system_prompt_lock:
            if tool not in system_prompt_cache:
                path = os.path.join(PROMPTS_DIR, "system_prompts",
                                    f"{tool}.txt")
                assert os.path.exists(path), \
                    f"Missing system prompt file: {path}"
                with open(path, "r", encoding="utf-8") as f:
                    system_prompt_cache[tool] = f.read()
            return system_prompt_cache[tool]

    workers = max(1, args.workers)
    print(f"Parallel workers:   {workers}")

    if workers == 1:
        for i, tpl in enumerate(templates, start=1):
            _process_template(
                tpl, i, len(templates),
                attempt_limit=attempt_limit,
                time_limit=time_limit,
                log_root=args.log_root,
                coherent_prompt=coherent_prompt,
                fill_todo_inst=fill_todo_inst,
                error_feedback_inst=error_feedback_inst,
                get_system_prompt=get_system_prompt,
                model=args.model,
            )
        return

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {
            pool.submit(
                _process_template,
                tpl, i, len(templates),
                attempt_limit=attempt_limit,
                time_limit=time_limit,
                log_root=args.log_root,
                coherent_prompt=coherent_prompt,
                fill_todo_inst=fill_todo_inst,
                error_feedback_inst=error_feedback_inst,
                get_system_prompt=get_system_prompt,
                model=args.model,
            ): tpl
            for i, tpl in enumerate(templates, start=1)
        }
        completed = 0
        for fut in as_completed(futures):
            completed += 1
            tpl = futures[fut]
            label = (f"{tpl['year']}/{tpl['taskname']}/{tpl['tool']}/"
                     f"{tpl['split_id']}")
            try:
                fut.result()
                print(f"[{completed}/{len(templates)}] OK   {label}")
            except Exception as exc:
                print(f"[{completed}/{len(templates)}] FAIL {label}  {exc!r}")


if __name__ == "__main__":
    main()
