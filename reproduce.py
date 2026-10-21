"""Build the exact local review package and audit its named theorem axioms.

Python standard library only. Does not upload files or contact prize staff.
Lake may download the pinned Lean toolchain if it is not installed already.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

from verify_sets import verify


BASE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = [
    "RazReimer.counterexample", "RazReimer.not_reimerStrengthening",
    "RazReimerPredicates.every_predicate_represented",
    "RazReimerPredicates.shared_index_bijective",
    "RazReimerPredicates.condition_transfer",
    "RazReimerPredicates.condition_reflection",
    "RazReimerPredicates.condition_iff",
    "RazReimerPredicates.frequency_transfer",
    "RazReimerPredicates.A_nontrivial",
    "RazReimerPredicates.A_frequencies",
    "RazReimerPredicates.A_not_unionClosed",
    "RazReimerPredicates.counterexample",
    "RazReimerPredicates.not_strengthening",
]


def run(command, name, logdir):
    start = time.monotonic()
    proc = subprocess.run(command, cwd=BASE, capture_output=True,
                          text=True, encoding="utf-8", errors="replace", timeout=240)
    output = proc.stdout + proc.stderr
    (logdir / (name + ".log")).write_text(output, encoding="utf-8")
    if proc.returncode:
        raise RuntimeError(name + " failed:\n" + output)
    return output, {"command": command, "exit_code": proc.returncode,
                    "seconds": round(time.monotonic() - start, 3)}


def without_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth and text[i:i+2] == "-/":
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text[i:i+2] == "--":
            stop = text.find("\n", i)
            i = len(text) if stop < 0 else stop
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"))
    parser.add_argument("--toolchain", help="Installed alias; exact Lean commit is still checked")
    args = parser.parse_args()
    if not args.lake:
        parser.error("Lake is not on PATH; supply --lake /path/to/lake")
    logdir = BASE / "verification"
    logdir.mkdir(exist_ok=True)
    source_hashes = {}
    expected = json.loads((BASE / "source-manifest.json").read_text(encoding="utf-8"))
    for name, digest in expected["sha256"].items():
        data = (BASE / name).read_bytes()
        source_hashes[name] = hashlib.sha256(data).hexdigest()
        if source_hashes[name] != digest:
            raise RuntimeError("Source hash mismatch: " + name)
        if name.endswith(".lean"):
            code = without_comments(data.decode("utf-8"))
            if re.search(r"\b(sorry|admit|native_decide|sorryAx)\b", code):
                raise RuntimeError("Forbidden proof token in " + name)
            if re.search(r"(?m)^\s*axiom\b", code):
                raise RuntimeError("Custom axiom declaration in " + name)
    lake = [args.lake] + (["+" + args.toolchain] if args.toolchain else [])
    version, vstep = run(lake + ["env", "lean", "--version"], "version", logdir)
    if "version 4.35.0," not in version or expected["lean_commit"] not in version:
        raise RuntimeError("Unexpected Lean version or commit: " + version)
    had_project_build = (BASE / ".lake" / "build").exists()
    _, build = run(lake + ["build"], "build", logdir)
    audit_text, audit = run(lake + ["env", "lean", "Audit.lean"], "axioms", logdir)
    footprints = {}
    for line in audit_text.splitlines():
        match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
        empty = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
        if match:
            names = set(filter(None, (a.strip() for a in match[2].split(","))))
            if not names <= ALLOWED:
                raise RuntimeError("Unexpected axiom: " + line)
            footprints[match[1]] = sorted(names)
        elif empty:
            footprints[empty[1]] = []
    if set(footprints) != set(TARGETS):
        raise RuntimeError("Missing or unexpected target axiom report: " + audit_text)
    result = {
        "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "pass": True,
        "lean_version": version.strip(),
        "source_sha256": source_hashes,
        "project_build_dir_existed_before_build": had_project_build,
        "upstream_std_artifacts_reused": True,
        "steps": {"version": vstep, "build": build, "axioms": audit},
        "axiom_footprints": footprints,
        "independent_explicit_sets": verify(),
        "independent_kernel_checker_run": False,
        "mathdb_statement_id": 363118,
        "jsp_id": None,
        "priority_or_prize_eligibility_confirmed": False,
        "external_submission_made_by_this_script": False,
    }
    (logdir / "result.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"pass": True, "theorems_audited": len(footprints),
                      "project_cache_reused": had_project_build,
                      "report": str(logdir / "result.json")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
