"""
Feedback-driven driver for VerifyThisBench (the full benchmark).

Workflow (per challenge):
  1. Read the challenge description (and optional per-tool data-structure
     definition) from `../VerifyThisBenchDS/dataset.json`.
  2. For each task in the challenge:
     a. Ask the LLM to write code that addresses the task, with the
        running `task_context` carrying turns from previously-completed
        tasks in the same challenge.
     b. Run a coherence check on the response.
     c. Verify the generated code with the formal tool.
     d. On verification failure, feed the error log back to the LLM and
        retry, up to `--attempt` total tries.
     e. On success (or once the attempt budget is exhausted), the
        accumulated `task_context` carries forward to the next task.

System prompt assembly (matches the original research pipeline):
  * Base system prompt:  ../prompts/system_prompts/<tool>.txt
  * Spec-ABI prompt:     ../prompts/spec_abi_prompts/<tool>.txt   (appended)
  * Coherence prompt:    ../prompts/coherent_prompt.txt           (used per
                                                                   coherence
                                                                   check)

Resume support: pass `--resume` to skip per-task work that's already
finished on disk and seed the first unfinished task with the saved
conversation from the most recently-completed task.

After a run, point `run_spec_test.py` at the same `--log-root` to
generate spec tests on top of the verified solutions.

Configuration:
  * The OpenAI client reads its base URL and API key from environment
    variables (`OPENAI_BASE_URL`, `OPENAI_API_KEY`).
  * Default model is set in `DEFAULT_MODEL`; override with `--model`.
"""

import argparse
import json
import os
import re
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


def extract_coherence(response):
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
# Verifier dispatch
# ---------------------------------------------------------------------------

def eval_code(tool, code_string, tag, timeout=60):
    """Run the chosen formal-verification tool on the given code."""
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
# Dataset loading
# ---------------------------------------------------------------------------

def load_dataset(dataset_path: str) -> list:
    """Load challenge entries from a VerifyThisBenchDS-style JSON file."""
    with open(dataset_path) as f:
        data = json.load(f)
    return data.get("challenges", [])


# ---------------------------------------------------------------------------
# Resume support
# ---------------------------------------------------------------------------

_TASK_CTX_RE = re.compile(r"^task_context_(\d+)_(\d+)\.txt$")
_VERIF_RE = re.compile(r"^verification_(\d+)_(\d+)\.txt$")


def _load_last_assistant(task_dir: str, task_num: int, attempt: int):
    """Read refine_context_{task_num}_{attempt}.txt and return the final
    assistant message content, or None if it can't be recovered."""
    path = os.path.join(task_dir, f"refine_context_{task_num}_{attempt}.txt")
    if not os.path.exists(path):
        return None
    try:
        with open(path) as f:
            ctx = json.load(f)
    except Exception:
        return None
    if not isinstance(ctx, list):
        return None
    for msg in reversed(ctx):
        if isinstance(msg, dict) and msg.get("role") == "assistant":
            content = msg.get("content", "")
            if isinstance(content, str):
                return content
    return None


def _task_is_finished(task_dir: str, task_num: int, attempt_limit: int):
    """Return (finished, finishing_attempt). A task is finished if any
    verification within the attempt budget succeeded, or if the budget was
    exhausted."""
    if not os.path.isdir(task_dir):
        return False, None

    verif_by_attempt = {}
    for fname in os.listdir(task_dir):
        m = _VERIF_RE.match(fname)
        if m and int(m.group(1)) == task_num:
            a = int(m.group(2))
            try:
                with open(os.path.join(task_dir, fname)) as f:
                    verif_by_attempt[a] = json.load(f)
            except Exception:
                verif_by_attempt[a] = None

    if not verif_by_attempt:
        return False, None

    for a in sorted(verif_by_attempt.keys()):
        v = verif_by_attempt[a]
        if isinstance(v, dict) and v.get("succeed") and not v.get("partial"):
            return True, a

    max_attempt = max(verif_by_attempt.keys())
    if max_attempt >= attempt_limit:
        return True, max_attempt
    return False, None


def _find_resume_point(log_root: str, year: str, taskname: str,
                       tasks: list, attempt_limit: int,
                       base_context: list):
    """Walk the per-challenge log tree and return (start_idx, task_context).

    A task is finished if a saved task_context file exists, OR a
    verification within the attempt budget succeeded, OR the budget was
    exhausted. We accumulate task_context the same way the live pipeline
    does. Stop at the first non-finished task and return its index."""
    ch_dir = os.path.join(log_root, year, taskname)
    if not os.path.isdir(ch_dir):
        return 0, None

    task_context = list(base_context)
    last_finished_idx = -1

    for idx, task in enumerate(tasks):
        task_num = idx + 1
        task_dir = os.path.join(ch_dir, str(task_num))
        if not os.path.isdir(task_dir):
            break

        # Easy path: saved task_context file gives us the conversation.
        ctx_matches = []
        for fname in os.listdir(task_dir):
            m = _TASK_CTX_RE.match(fname)
            if m and int(m.group(1)) == task_num:
                ctx_matches.append((int(m.group(2)), fname))
        if ctx_matches:
            ctx_matches.sort()
            latest = os.path.join(task_dir, ctx_matches[-1][1])
            try:
                with open(latest) as f:
                    task_context = json.load(f)
                last_finished_idx = idx
                continue
            except Exception:
                pass  # fall through to reconstruction

        finished, final_attempt = _task_is_finished(
            task_dir, task_num, attempt_limit)
        if not finished:
            break

        # Reconstruct task_context from the finishing turn.
        task_content = task.get("content", "")
        response = _load_last_assistant(task_dir, task_num, final_attempt) or ""
        task_context = task_context + [
            {"role": "user", "content": task_content},
            {"role": "assistant", "content": response},
        ]
        last_finished_idx = idx

    return (
        last_finished_idx + 1,
        task_context if last_finished_idx >= 0 else None,
    )


# ---------------------------------------------------------------------------
# Per-challenge worker
# ---------------------------------------------------------------------------

def _process_challenge(
    challenge,
    *,
    tool,
    attempt_limit,
    time_limit,
    log_root,
    system_prompt,
    coherent_prompt,
    error_feedback_inst,
    model,
    resume,
):
    """Process every task within a single challenge end-to-end. Tasks
    inside a challenge run sequentially so `task_context` can accumulate
    turns across them; challenges themselves may be processed concurrently
    by the caller."""
    year = str(challenge.get("year", ""))
    taskname = challenge.get("name", "")
    description = challenge.get("description", "") or ""

    print(f"\n[challenge] {year}/{taskname}")
    if not description:
        print(f"  Missing description, skipping.")
        return

    # Optional: per-tool data-structure definition the model should reuse.
    datastructure_raw = (challenge.get("data_structures") or {}) \
        .get(tool, "").strip()
    datastructure_def = (
        f"\n\nData structure definition to use:\n{datastructure_raw}"
        if datastructure_raw else ""
    )

    task_context = [
        {
            "role": "user",
            "content": (
                "Target this verification problem; plan out your steps and "
                "write your final answer:\n\n"
                f"{description}{datastructure_def}"
            ),
        },
        {"role": "assistant", "content": "OK, I'm ready to help."},
    ]

    tasks = challenge.get("tasks", []) or []

    start_idx = 0
    if resume:
        resume_idx, resumed_ctx = _find_resume_point(
            log_root, year, taskname, tasks, attempt_limit, task_context,
        )
        if resume_idx >= len(tasks):
            print(f"  resume: all {len(tasks)} tasks already finished — "
                  f"skipping.")
            return
        if resume_idx > 0:
            print(f"  resume: skipping tasks 1..{resume_idx} "
                  f"(finished on disk); starting at task {resume_idx + 1}.")
            if resumed_ctx is not None:
                task_context = resumed_ctx
        start_idx = resume_idx

    for idx, task in enumerate(tasks):
        if idx < start_idx:
            continue
        task_id = task.get("id") or f"task{idx + 1}"
        task_content = task.get("content", "") or ""
        print(f"  [task {idx + 1}/{len(tasks)}] {task_id}")
        attempt = 1
        error = None
        starttime = time.time()
        refine_context = task_context.copy()

        while attempt <= attempt_limit:
            start = time.time()
            query_inst = (
                task_content if attempt == 1
                else error_feedback_inst + f"{error}"
            )

            response = form_query_response(
                query_inst, system_prompt, task_context, model=model)
            code_response, tag = extract_code(response)
            code_response_time = time.time()
            print(f"    attempt {attempt} code response: "
                  f"{code_response_time - start:.2f}s")

            log_dir = os.path.join(log_root, year, taskname, str(idx + 1))
            os.makedirs(log_dir, exist_ok=True)

            code_path = os.path.join(
                log_dir, f"code_response_{idx + 1}_{attempt}.txt")
            save_to_file(code_path, code_response or "NO CODE FOUND")

            refine_context.extend([
                {"role": "user", "content": query_inst},
                {"role": "assistant", "content": response},
            ])
            context_path = os.path.join(
                log_dir, f"refine_context_{idx + 1}_{attempt}.txt")
            save_to_file(context_path, json.dumps(refine_context, indent=4))

            coherence_check = form_query_response(
                coherent_prompt, system_prompt,
                task_context + [
                    {"role": "user", "content": task_content},
                    {"role": "assistant", "content": response},
                ],
                model=model,
            )
            coherence_response = extract_coherence(coherence_check)
            coherence_response_time = time.time()
            print(f"    attempt {attempt} coherence response: "
                  f"{coherence_response_time - code_response_time:.2f}s")
            correctness_path = os.path.join(
                log_dir, f"coherence_check_{idx + 1}_{attempt}.txt")
            save_to_file(correctness_path, coherence_check,
                         coherence_response or "NO COHERENCE FOUND")

            verification_path = os.path.join(
                log_dir, f"verification_{idx + 1}_{attempt}.txt")
            if not code_response:
                attempt += 1
                error = "Your previous attempt did not contain any code."
                save_to_file(verification_path, json.dumps("NO CODE FOUND"))
                continue

            print(f"    verifying {year}/{taskname}/{task_id} attempt {attempt}")
            start = time.time()
            result = eval_code(tool, code_response, tag, time_limit)
            print(f"    eval: {time.time() - start:.2f}s")
            save_to_file(verification_path, json.dumps(result, indent=2))
            error = (result["out"] + result["err"]
                     if not result["timed_out"]
                     else "Execution timed out.")

            if result["succeed"] and not result["partial"]:
                # Carry the verified turn forward into task_context for
                # subsequent tasks in the same challenge.
                task_context.extend([
                    {"role": "user", "content": task_content},
                    {"role": "assistant", "content": response},
                ])
                ctx_path = os.path.join(
                    log_dir, f"task_context_{idx + 1}_{attempt}.txt")
                save_to_file(ctx_path, json.dumps(task_context, indent=4))
                break

            # Final attempt: still save accumulated context so downstream
            # consumers can see the conversation history.
            if attempt == attempt_limit:
                task_context.extend([
                    {"role": "user", "content": task_content},
                    {"role": "assistant", "content": response},
                ])
                ctx_path = os.path.join(
                    log_dir, f"task_context_{idx + 1}_{attempt}.txt")
                save_to_file(ctx_path, json.dumps(task_context, indent=4))

            attempt += 1

        print(f"  [{year}/{taskname}/{task_id}] elapsed "
              f"{time.time() - starttime:.2f}s")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tool", type=str, required=True,
                        help="Verification tool name (dafny / why3 / verus / "
                             "framac / verifast / vercors / cbmc).")
    parser.add_argument("--attempt", type=int, required=True,
                        help="Maximum attempts per task during verification "
                             "refinement.")
    parser.add_argument("--timelimit", type=int, required=True,
                        help="Time limit (seconds) for each tool invocation.")
    parser.add_argument("--dataset", type=str,
                        default="../VerifyThisBenchDS/dataset.json",
                        help="Path to VerifyThisBenchDS/dataset.json.")
    parser.add_argument("--year", action="append", default=None,
                        help="Restrict to challenges from these year(s) "
                             "(repeatable).")
    parser.add_argument("--task-filter", action="append", default=None,
                        help="Restrict to challenges whose name matches "
                             "(repeatable).")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL,
                        help=f"LLM model name (default: {DEFAULT_MODEL}).")
    parser.add_argument("--log-root", type=str, default=DEFAULT_LOG_ROOT,
                        help=f"Output log root (default: {DEFAULT_LOG_ROOT}).")
    parser.add_argument(
        "--workers", type=int, default=1,
        help="Number of CHALLENGES to process in parallel (default: 1). "
             "Tasks within a challenge stay sequential so task_context can "
             "accumulate.",
    )
    parser.add_argument("--resume", action="store_true",
                        help="Skip tasks already finished on disk and seed "
                             "the first unfinished task with the saved "
                             "conversation from the most recent completed "
                             "task.")
    args = parser.parse_args()

    # System prompt = base + spec-ABI prompt (the ABI fragment defines the
    # main_spec_pre / main_spec_post calling convention each tool expects).
    system_prompt_file = os.path.join(
        PROMPTS_DIR, "system_prompts", f"{args.tool}.txt")
    assert os.path.exists(system_prompt_file), \
        f"Missing system prompt: {system_prompt_file}"
    system_prompt = open(system_prompt_file).read()
    abi_prompt_file = os.path.join(
        PROMPTS_DIR, "spec_abi_prompts", f"{args.tool}.txt")
    if os.path.exists(abi_prompt_file):
        system_prompt += open(abi_prompt_file).read()
    else:
        print(f"Warning: missing ABI prompt: {abi_prompt_file}")

    coherent_prompt_file = os.path.join(PROMPTS_DIR, "coherent_prompt.txt")
    with open(coherent_prompt_file, "r") as f:
        coherent_prompt = f.read()

    error_feedback_inst = "Here is the error log. Fix the issues.\n"

    print(f"Tool:      {args.tool}")
    print(f"Model:     {args.model}")
    print(f"Log root:  {args.log_root}")
    print(f"Attempts:  {args.attempt}")
    print(f"Timelimit: {args.timelimit}s")
    if args.resume:
        print(f"Resume:    on")

    challenges = load_dataset(args.dataset)
    year_filter = set(args.year) if args.year else None
    name_filter = set(args.task_filter) if args.task_filter else None

    filtered = [
        c for c in challenges
        if (not year_filter or str(c.get("year")) in year_filter)
        and (not name_filter or c.get("name") in name_filter)
    ]
    filtered.sort(key=lambda c: (str(c.get("year", "")), c.get("name", "")))

    print(f"Challenges to process: {len(filtered)}")

    workers = max(1, args.workers)
    print(f"Workers: {workers}")

    def run_one(challenge):
        _process_challenge(
            challenge, tool=args.tool, attempt_limit=args.attempt,
            time_limit=args.timelimit, log_root=args.log_root,
            system_prompt=system_prompt, coherent_prompt=coherent_prompt,
            error_feedback_inst=error_feedback_inst, model=args.model,
            resume=args.resume,
        )

    if workers == 1:
        for c in filtered:
            run_one(c)
        return

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(run_one, c): c for c in filtered}
        completed = 0
        for fut in as_completed(futures):
            completed += 1
            c = futures[fut]
            label = f"{c.get('year')}/{c.get('name')}"
            try:
                fut.result()
                print(f"[{completed}/{len(filtered)}] OK   {label}")
            except Exception as exc:
                print(f"[{completed}/{len(filtered)}] FAIL {label}  {exc!r}")


if __name__ == "__main__":
    main()
