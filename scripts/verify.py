"""
Docker-backed verifier dispatch for VerifyThisBench.

Each `eval_<tool>` function writes the candidate code to a temporary file,
runs the corresponding verifier inside its Docker image, and returns a
uniform result dict:

    {
        "out":             stdout from the verifier,
        "err":             stderr from the verifier (or timeout marker),
        "returncode":      verifier's process return code (or -1 on timeout),
        "succeed":         the verifier reported a clean success,
        "timed_out":       the run exceeded `timeout` seconds,
        "compilation_err": the verifier failed to even compile / parse,
        "partial":         some assertions passed and some failed,
    }

Two flavours of entry points are provided per tool where they differ:
  * `eval_<tool>`       — used in the main verification loop (production).
  * `eval_<tool>_spec`  — used in the spec-test refinement loop. The two
                          differ only in the verifier flags / suffix
                          conventions tuned for the spec-test artifact
                          shape.

Every `eval_*` function relies on `docker_run.run_docker_with_timeout` to
handle the timeout-and-cleanup envelope around `docker run`.
"""

import os
import tempfile
import json
import re

from docker_run import run_docker_with_timeout


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def ensure_verus_main(code: str) -> str:
    """Verus needs `fn main() { }` at the top level. Add one if missing."""
    if re.search(r"\bfn\s+main\s*\(", code):
        return code
    if "verus! {" in code:
        return code.replace("verus! {", "fn main() {}\n\nverus! {", 1)
    return "fn main() {}\n\n" + code


# ---------------------------------------------------------------------------
# VerCors  (production: eval_vercors / spec-test: eval_vercors_spec)
# ---------------------------------------------------------------------------

def eval_vercors(code, timeout=60, lang='c', max_errs=5, json_mode=True,
                 func_name=None) -> dict:
    """Verify a VerCors candidate. `lang` selects the file extension used for
    the temporary file (e.g. 'c', 'java', 'pvl')."""
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=f".{lang}",
                                     dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    container_file_path = f"/home/{filename}"
    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "vercors:try",
        "vct", container_file_path,
    ]
    completed, timed_out = run_docker_with_timeout(cmd, timeout=timeout)
    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out
               else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": (not timed_out) and completed.returncode == 2,
        "partial":  (not timed_out) and completed.returncode == 1,
    }


def eval_vercors_spec(code, timeout=60, max_errs=5, json_mode=True,
                      func_name=None) -> dict:
    """Spec-test variant: forces a `.pvl` source file."""
    return eval_vercors(code, timeout=timeout, lang="pvl",
                        max_errs=max_errs, json_mode=json_mode,
                        func_name=func_name)


# ---------------------------------------------------------------------------
# CBMC
# ---------------------------------------------------------------------------

def eval_cbmc(code, timeout=60, max_errs=5, json_mode=True,
              func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".c",
                                     dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    container_file_path = f"/home/{filename}"

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "cbmc:try",
        "cbmc", "-z3", "--unwind", "11", "--trace", container_file_path,
    ]
    completed, timed_out = run_docker_with_timeout(cmd, timeout=timeout)
    os.unlink(f.name)

    match = re.search(r'\b(\d+)\s+of\s+(\d+)\s+failed\b',
                      str(completed.stdout))
    partial = True
    none_verified = False
    match_flag = False
    if match:
        failed, total = int(match.group(1)), int(match.group(2))
        none_verified = failed == total
        partial = failed < total and failed != 0
        match_flag = True

    if completed.stderr:
        return {
            "out": completed.stdout,
            "err": completed.stderr,
            "returncode": completed.returncode if not timed_out else -1,
            "succeed": False,
            "timed_out": False,
            "compilation_err": True,
            "partial": False,
        }

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out
               else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0)
                   and not none_verified,
        "timed_out": timed_out,
        "compilation_err": (not timed_out) and (completed.returncode == 6)
                           and not match_flag,
        "partial": (not timed_out) and match_flag
                   and (not completed.returncode == 0),
    }


# ---------------------------------------------------------------------------
# VeriFast  (production: eval_verifast / spec-test: eval_verifast_spec)
# ---------------------------------------------------------------------------

def eval_verifast(code, timeout=5, language="java", max_errs=5,
                  json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=f".{language}",
                                     dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    container_file_path = f"/home/{filename}"
    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "verifast:try",
        "verifast", "-c", "-disable_overflow_check", "-json",
        container_file_path,
    ]
    completed, timed_out = run_docker_with_timeout(cmd, timeout=timeout)
    os.unlink(f.name)

    compilation_error = (not timed_out) and (
        "StaticError" in completed.stdout or "Parse error" in completed.stdout)
    symbolic_error = (not timed_out) and (
        "SymbolicExecutionError" in completed.stdout
        or "Symbolic execution error" in completed.stdout)
    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out
               else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": completed.returncode == 0
                   and not compilation_error and not symbolic_error,
        "timed_out": timed_out,
        "compilation_err": compilation_error,
        "partial": symbolic_error,
    }


def eval_verifast_spec(code, timeout=5, language="c", max_errs=5,
                       json_mode=True, func_name=None) -> dict:
    """Spec-test variant: defaults to `.c` (vs the prod default of `.java`)."""
    return eval_verifast(code, timeout=timeout, language=language,
                         max_errs=max_errs, json_mode=json_mode,
                         func_name=func_name)


# ---------------------------------------------------------------------------
# Why3
# ---------------------------------------------------------------------------

def eval_why3(
    code,
    timeout=60,
    timelimit=10,
    max_errs=5,
    json_mode=True,
    func_name=None,
    apply_transforms=None,
) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".mlw",
                                     dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    container_file_path = f"/home/{filename}"

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "why3:try",
        "why3", "prove", "-P", "cvc4", "--timelimit", f"{timeout}",
    ]
    for transform in apply_transforms or []:
        cmd.append(f"--apply-transform={transform}")
    cmd.append(container_file_path)
    completed, timed_out = run_docker_with_timeout(cmd, timeout=timeout)
    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out
               else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode == 1),
        "partial": not timed_out and (completed.returncode == 2),
    }


# ---------------------------------------------------------------------------
# Dafny  (production: eval_dafny / spec-test: eval_dafny_spec)
# ---------------------------------------------------------------------------

def eval_dafny(code, timeout=60, max_errs=5, json_mode=True,
               func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".dfy",
                                     dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    container_file_path = f"/home/{filename}"
    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "dafny:try",
        "dafny", "verify", "--allow-warnings", container_file_path,
    ]
    completed, timed_out = run_docker_with_timeout(cmd, timeout=timeout)
    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out
               else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode == 2),
        "partial": not timed_out and (completed.returncode == 4),
    }


# Dafny's spec-test variant is identical to the production variant; alias.
eval_dafny_spec = eval_dafny


# ---------------------------------------------------------------------------
# Verus
# ---------------------------------------------------------------------------

def eval_verus(code, timeout=60, max_errs=5, json_mode=True,
               func_name=None) -> dict:
    code = ensure_verus_main(code)

    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".rs",
                                     dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    multiple_errors = f"--multiple-errors {max_errs}" if max_errs > 0 else ""
    err_format = "--output-json --error-format=json" if json_mode else ""
    cmd = (f"/verus/verus {multiple_errors} {err_format}").split()
    cmd += [filename]
    if func_name:
        cmd += ["--time", "--verify-function", func_name, "--verify-root"]

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home", "verus:try"] + cmd
    completed, timed_out = run_docker_with_timeout(cmd, timeout=timeout)
    os.unlink(f.name)

    try:
        result = json.loads(completed.stdout)
        verified = result["verification-results"].get("verified", 0)
        errors = result["verification-results"].get("errors", 0)
    except Exception:
        verified = 0
        errors = 0

    # A "vacuous" verus run is one where the proof discharged but zero
    # verification conditions actually existed (verified == errors == 0,
    # typically because the LLM-generated code stripped or never produced
    # `requires`/`ensures`). Verus reports `success: true` for these even
    # though no real proof obligations were checked. Treat them as partial
    # (and clear `succeed`) so downstream consumers don't count them as
    # genuine pass@K successes.
    compilation_error = (verified == errors == 0)
    raw_succeed = (not timed_out) and (completed.returncode == 0)
    is_vacuous = raw_succeed and compilation_error
    succeed_flag = raw_succeed and not is_vacuous
    if is_vacuous:
        partial_flag = True
    else:
        partial_flag = (not timed_out) and (completed.returncode != 0) \
                       and not compilation_error
    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out
               else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": succeed_flag,
        "timed_out": timed_out,
        "compilation_err": compilation_error and not timed_out,
        "partial": partial_flag,
    }


# ---------------------------------------------------------------------------
# Frama-C  (production: eval_framac / spec-test: eval_framac_spec)
# ---------------------------------------------------------------------------

def _eval_framac_common(code, timeout, prover) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".c",
                                     dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    container_file_path = f"/home/{filename}"

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "framac:try",
        "frama-c", "-wp", "-wp-rte", "-wp-prover", prover,
    ]
    if prover == "z3":
        cmd += ["-wp-print"]
    cmd += [container_file_path]
    completed, timed_out = run_docker_with_timeout(cmd, timeout=timeout)
    os.unlink(f.name)

    partial = True
    no_goal = True
    match = re.search(r'Proved goals:\s+(\d+)\s*/\s*(\d+)',
                      str(completed.stdout))
    match_flag = False
    if match:
        proved, total = int(match.group(1)), int(match.group(2))
        no_goal = total == 0
        partial = proved < total
        match_flag = True

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out
               else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0)
                   and (not partial) and (not no_goal),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode != 0),
        "partial": not timed_out and (partial or no_goal) and match_flag,
    }


def eval_framac(code, timeout=60, max_errs=5, json_mode=True,
                func_name=None) -> dict:
    """Production variant uses alt-ergo as the WP prover."""
    return _eval_framac_common(code, timeout=timeout, prover="alt-ergo")


def eval_framac_spec(code, timeout=60, max_errs=5, json_mode=True,
                     func_name=None) -> dict:
    """Spec-test variant uses z3 + verbose proof printing."""
    return _eval_framac_common(code, timeout=timeout, prover="z3")
