# VerifyThisBench: Joint Evaluation of Code, Specifications, and Proofs

Official benchmark and evaluation suite for the paper **"VerifyThisBench: Joint Evaluation of Code, Specifications, and Proofs"** (NeurIPS 2026, Evaluations and Datasets Track).

### 🏆 Leaderboards

#### VerifyThisBench — Human-verified (intent-aligned)

Passing the verifier only shows that a solution matches the model's *own* specification, which may be weak or vacuous. This leaderboard counts solutions that **human inspection confirmed match the intended task** (Table 1 in the paper), out of all 1,078 task × verifier pairs, with refinement.

| Rank | Model                               | Human-verified | Verifier acceptance |
|------|-------------------------------------|----------------|---------------------|
| 1    | GPT-5.4 (2026-03-05)                | **21 (1.95%)** | 213 (19.76%)        |
| 2    | DeepSeek-V4-Flash (2026-04-24)      | 9 (0.83%)      | 176 (16.33%)        |
| 3    | GPT-5.4-mini (2026-03-17)           | 8 (0.74%)      | **370 (34.32%)**    |
| 4    | Qwen3-Coder-Flash (2025-09-17)      | 3 (0.27%)      | 171 (15.86%)        |
| 5    | Llama-3.3-70B-Instruct (2024-12-06) | 1 (0.09%)      | 70 (6.49%)          |
| 6    | GPT-4o-mini (2024-07-18)            | 0              | 31 (2.88%)          |

The two leaderboards below report **verifier acceptance rate**: **Zero-shot** = the verifier accepts the first attempt; **Refinement** = the verifier accepts within 5 attempts, with verifier feedback between attempts. Rates are over all task × verifier pairs (1,078 for VerifyThisBench, 580 for VerifyThisBenchXS). They are an upper bound on capability, not a ranking of correctness.

#### VerifyThisBench — Verifier acceptance

| Rank | Model                               | Zero-shot  | Refinement |
|------|-------------------------------------|------------|------------|
| 1    | GPT-5.4-mini (2026-03-17)           | **17.35%** | **34.32%** |
| 2    | GPT-5.4 (2026-03-05)                | 7.05%      | 19.76%     |
| 3    | DeepSeek-V4-Flash (2026-04-24)      | 4.64%      | 16.33%     |
| 4    | Qwen3-Coder-Flash (2025-09-17)      | 8.63%      | 15.86%     |
| 5    | Llama-3.3-70B-Instruct (2024-12-06) | 2.04%      | 6.49%      |
| 6    | GPT-4o-mini (2024-07-18)            | 0.83%      | 2.88%      |

#### VerifyThisBenchXS — Verifier acceptance

| Rank | Model                               | Zero-shot  | Refinement |
|------|-------------------------------------|------------|------------|
| 1    | GPT-5.4-mini (2026-03-17)           | 2.76%      | **15.69%** |
| 2    | DeepSeek-V4-Flash (2026-04-24)      | 3.10%      | 13.28%     |
| 3    | GPT-5.4 (2026-03-05)                | **3.28%**  | 12.59%     |
| 4    | Llama-3.3-70B-Instruct (2024-12-06) | 1.72%      | 2.93%      |
| 5    | Qwen3-Coder-Flash (2025-09-17)      | 1.38%      | 2.76%      |
| 6    | GPT-4o-mini (2024-07-18)            | 1.38%      | 1.38%      |

### Introduction
VerifyThisBench is a new benchmark designed to evaluate LLMs on end-to-end program verification tasks that require interpreting natural language problem descriptions, formulating formal specifications, generating code, and constructing correctness proofs.

### Description
You can find the dataset under `/VerifyThisBenchDS`, organized by years. For each challenge, you can find its overall description.txt and the files to individual sub-tasks.

The relaxed version can be found under `/VerifyThisBenchXS`, organized by years and tools. `solution.*` is the human-written solution. Variants are `fill-implementation`, `fill-specification`, `fill-loop-invariant`. `split` indicates that a partial solution of that form is given.

Seed test cases for the spec-testing stage live under `/VerifyThisBenchTest`, organized by `<year>/<taskname>/seed_tests.json`. Each seed carries a `task` field (`task1`, `task2`, …) so that the spec-test driver can restrict the seeds it shows the model to the cumulative scope of the current task (i.e. for `task_idx=3` it only passes seeds tagged `task1`/`task2`/`task3`).

Additionally, you can find example system prompts and the coherent prompt under `/prompts`. Docker files to set up the evaluation environments are available under `/envs`. Example scripts to evaluate LLMs can be found under `/scripts`.

```
prompts/
├── coherent_prompt.txt           # used per coherence check
├── system_prompts/<tool>.txt     # base system prompt per verifier
└── spec_abi_prompts/<tool>.txt   # appended to system prompt — defines the
                                  # main_spec_pre / main_spec_post calling
                                  # convention each verifier expects
scripts/
├── query_with_feedback.py            # VerifyThisBench driver
├── query_relaxed_with_feedback.py    # VerifyThisBenchXS driver
├── run_spec_test.py                  # spec-test stage (post-verification)
├── verify.py                         # Docker-backed verifier dispatch
├── docker_run.py                     # docker subprocess + timeout helper
└── spectest_prompts/<tool>.txt       # per-verifier spec-test prompt
```

### Example Usage

#### Installation
The drivers need Python 3.10+ and Docker. From the repository root:
```bash
pip install -r requirements.txt
```

#### Verification Tool Setup
Each verifier runs in its own Docker image. `scripts/verify.py` calls the images by the tags `cbmc:try`, `dafny:try`, `framac:try`, `vercors:try`, `verifast:try`, `verus:try` and `why3:try`, so build each one under that tag from the repository root:
```bash
docker build -t dafny:try    envs/Dafny
docker build -t verus:try    envs/Verus
docker build -t why3:try     envs/Why3
docker build -t framac:try   envs/FramaC
docker build -t verifast:try envs/VeriFast
docker build -t vercors:try  envs/VerCors
docker build -t cbmc:try     envs/CBMC
```
The Dockerfiles pin the tool versions used in the paper: Verus 0.2025.04.03.0f22710, Why3 1.6.0, Frama-C 30.0, VeriFast 25.02, Dafny 4.10.0, VerCors 2.3.0 and CBMC 6.5.0. You only need the images for the tools you plan to run.

#### Running Experiments
Run the drivers from the `scripts/` directory; default paths to the datasets and prompts are relative to it. The OpenAI client reads its base URL and API key from environment variables:
```bash
export OPENAI_BASE_URL="https://openrouter.ai/api/v1"
export OPENAI_API_KEY="sk-..."
```

The paper's settings are 5 attempts, a 120-second verifier time limit for generation, and a 600-second limit for spec testing; the examples below use them.

Three end-to-end scripts:

##### 1. Solve VerifyThisBench challenges with refinement
`query_with_feedback.py` iterates over the full benchmark. For each challenge it walks the per-task list sequentially — so `task_context` accumulates across tasks — asking the LLM to write code for each task, running a coherence check, verifying with the formal tool, and retrying with the error log as refinement up to `--attempt` times.

The system prompt is built from `prompts/system_prompts/<tool>.txt` plus the appended `prompts/spec_abi_prompts/<tool>.txt` (the ABI fragment defines the `main_spec_pre` / `main_spec_post` calling convention each verifier expects), and `prompts/coherent_prompt.txt` is fed to the per-attempt coherence check.

```bash
cd scripts
python query_with_feedback.py --tool dafny --attempt 5 --timelimit 120
```

Useful flags:
* `--year 2023` (repeatable) — restrict to specific year(s).
* `--task-filter "List Reversal"` (repeatable) — restrict to specific challenge names.
* `--model openai/gpt-5.4` — pick a different LLM.
* `--workers 4` — process challenges in parallel (tasks within a challenge stay sequential so context accumulates).
* `--resume` — skip per-task work that's already finished on disk and seed the first unfinished task with the saved conversation from the most-recent completed task.

Outputs land under `--log-root` (default `../results`), one directory tree per `<year>/<taskname>/<task_idx>/`:
```
<log-root>/<year>/<taskname>/<task_idx>/
    code_response_<task_idx>_<attempt>.txt   # extracted code from the LLM
    refine_context_<task_idx>_<attempt>.txt  # full conversation up to this attempt
    coherence_check_<task_idx>_<attempt>.txt # raw coherence response + parsed verdict
    verification_<task_idx>_<attempt>.txt    # verifier result JSON
    task_context_<task_idx>_<attempt>.txt    # cumulative challenge-level context (saved
                                             # at the finishing attempt)
```
This is the input layout `run_spec_test.py` expects.

##### 2. Solve VerifyThisBenchXS templates with feedback
`query_relaxed_with_feedback.py` iterates over the relaxed templates (spec-gen / impl-gen / inv-gen), asks the LLM to fill in the TODOs, runs the verifier, and retries with the error log as feedback up to `--attempt` times.

```bash
python query_relaxed_with_feedback.py --tool dafny --attempt 5 --timelimit 120
```

Useful flags:
* `--task-kind {all,spec-gen,impl-gen,inv-gen}` — restrict to a single subchallenge type.
* `--model`, `--workers`, `--log-root` — same as above.

##### 3. Run spec testing on existing verification results
`run_spec_test.py` consumes a results directory (e.g. produced by `query_with_feedback.py`) and, for every task whose latest verification within the pass@K window succeeded, generates seed-based spec-test assertions, re-runs the verifier on the augmented code, and (optionally) classifies the outcome with a second LLM call.

The script restricts the seed list it shows both LLM calls (the spec-test generator and the classifier) to the cumulative scope of the current task — for `task_idx=3` it includes seeds tagged `task1`, `task2`, `task3` and omits any seeds tagged `task4`+. This prevents the model from being asked to assert future-task properties on a solution that only addresses the current task.

```bash
python run_spec_test.py \
    --tool dafny \
    --log-root <path-to-your-verification-results> \
    --attempt 5 \
    --timelimit 600
```

The expected directory layout for the input is:
```
<log-root>/<year>/<taskname>/<task_idx>/
    verification_<task_idx>_<attempt>.txt   # verifier result JSON
    code_response_<task_idx>_<attempt>.txt  # the verified code
```

Each successful task gets four new artifacts written next to its existing files:
```
spectest_code_<task_idx>_<attempt>.txt              # generated test code
spectest_result_<task_idx>_<attempt>.txt            # verifier JSON result
spectest_classify_<task_idx>_<attempt>.txt          # raw classifier response
spectest_classify_result_<task_idx>_<attempt>.json  # parsed classification envelope
```

Useful flags:
* `--skip-classify` — generate and run spec tests only, without the second-stage classification call.
* `--force-test` / `--force-classify` / `--force` — re-run an existing stage instead of skipping when artifacts already exist on disk.
* `--year`, `--task-filter`, `--model`, `--workers` — same conventions as the other drivers.

### Citation
If you use VerifyThisBench, please cite:
```bibtex
@inproceedings{deng2026verifythisbench,
  title     = {VerifyThisBench: Joint Evaluation of Code, Specifications, and Proofs},
  author    = {Deng, Xun and Bayaz{\i}t, Bar{\i}{\c{s}} and Zhong, Sicheng and Veneris, Andreas and Long, Fan and Si, Xujie},
  booktitle = {Advances in Neural Information Processing Systems (NeurIPS), Evaluations and Datasets Track},
  year      = {2026}
}
```

### Acknowledgements and License
The challenge descriptions are taken from the [VerifyThis](https://www.pm.inf.ethz.ch/research/verifythis.html) competition series (2011–2024), and the human-written reference solutions in `VerifyThisBenchXS` (`solution.*` and the partial templates derived from them) come from competition participants and organizers. These materials remain the work of their original authors, and their original headers are kept as-is. We thank the VerifyThis organizers and participants for making them available.

The code, Docker environments, prompts, task decomposition, seed tests and other material created for this benchmark are released under the [MIT License](LICENSE). See [NOTICE](NOTICE) for details.
