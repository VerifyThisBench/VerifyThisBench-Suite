"""
Helper for running `docker run ...` commands with a hard timeout that also
tears down the underlying container. Stock `subprocess.run(..., timeout=...)`
only kills the local `docker` CLI process; the running container can outlive
the CLI and escape the `--rm` cleanup, leaving stale containers behind.

Usage:

    from docker_run import run_docker_with_timeout

    completed, timed_out = run_docker_with_timeout(cmd, timeout=60)
    # completed has .stdout, .stderr, .returncode (same shape as subprocess.run
    # returns). When timed_out is True, stdout/stderr/returncode reflect the
    # timeout and the container has been `docker kill`-ed.
"""

import subprocess
import uuid
from types import SimpleNamespace


def _inject_name(cmd, name):
    """Return a copy of *cmd* with `--name <name>` inserted right after the
    `run` subcommand. No-op if `run` isn't in the argv."""
    out = list(cmd)
    try:
        run_idx = out.index("run")
    except ValueError:
        return out
    out[run_idx + 1:run_idx + 1] = ["--name", name]
    return out


def _quiet(cmd, timeout=10):
    """Best-effort run; swallow everything."""
    try:
        subprocess.run(cmd, capture_output=True, timeout=timeout)
    except Exception:
        pass


def run_docker_with_timeout(cmd, timeout):
    """
    Run a `docker run ...` command with a hard timeout. On timeout:

      1. `docker kill <container>` so `--rm` can tear the container down.
      2. `docker rm -f <container>` as a belt-and-suspenders cleanup.
      3. SIGKILL the local `docker` CLI process and reap it.

    Returns `(completed, timed_out)` where `completed` has the same three
    attributes as `subprocess.CompletedProcess`: `.stdout`, `.stderr`,
    `.returncode`.
    """
    name = f"vtb_{uuid.uuid4().hex[:12]}"
    launch_cmd = _inject_name(cmd, name)

    proc = subprocess.Popen(
        launch_cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        return (
            SimpleNamespace(stdout=stdout, stderr=stderr, returncode=proc.returncode),
            False,
        )
    except subprocess.TimeoutExpired:
        # 1) Kill the running container so --rm cleans it up.
        _quiet(["docker", "kill", name])
        # 2) Force-remove in case the container slipped past --rm.
        _quiet(["docker", "rm", "-f", name])
        # 3) Make sure the local docker CLI process is gone.
        proc.kill()
        try:
            proc.communicate(timeout=5)
        except Exception:
            pass
        return (
            SimpleNamespace(
                stdout="",
                stderr=f"TimeoutExpired: command exceeded {timeout}s",
                returncode=-1,
            ),
            True,
        )
