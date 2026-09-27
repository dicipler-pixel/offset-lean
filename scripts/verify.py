#!/usr/bin/env python3
# SCRIPT: OFFSET-LEAN-VERIFY-01
"""Audit the Offset Lean library after `lake build`.

Why each check proves what it claims:

1. Axiom audit. `lake build` accepts a proof that uses `sorry` with only a
   warning, and a declared `axiom` would be accepted silently. `#print axioms`
   asks the kernel which axioms each theorem actually rests on. Requiring the
   answer to lie inside {propext, Classical.choice, Quot.sound} (the standard
   three every Mathlib theorem may use) rules out `sorry` (sorryAx), project
   axioms, and native_decide (Lean.ofReduceBool) for every named theorem.

2. Theorem inventory. The script discovers theorem names from the source files
   and fails if any expected module is missing or the count drops, so a theorem
   cannot silently disappear from the audit.

3. False controls. Each file in FalseControls/ states something deliberately
   false. It must FAIL to compile, and it must fail for a mathematical reason
   (unsolved goals, a failed tactic, a proposition proved false), not because of
   a typo or a missing name. This shows the checker can say no: a pipeline that
   accepts everything would pass the first two checks and fail this one.

4. Hashes. The SHA-256 of every source file is written to the report, so anyone
   can confirm the checked files are the files in the repository.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LIBRARY = [
    "Offset", "OffsetFock", "OffsetEndpoint", "EndpointProgress", "EndpointTransfer",
    "FiniteCovariance", "BandObstruction", "LaurentBoundary", "RiceMeleOddSymmetry", "BoundaryModel",
]
EXPECTED_LIBRARY_THEOREMS = 156
EXPECTED_HEADLINE_THEOREMS = 7
THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?theorem\s+([^\s:({\[]+)", re.M)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.M)
MATH_FAILURE = re.compile(
    r"unsolved goals|proved that the proposition.*false|tactic '.*' failed|"
    r"linarith failed|failed to prove|decide failed|norm_num failed|type mismatch",
    re.S | re.I)
INFRA_FAILURE = re.compile(
    r"unknown (?:module|identifier|constant|namespace)|unexpected token|"
    r"object file .* does not exist|invalid field", re.I)


LAST_OUTPUT = ""


def run(argv: list[str]) -> subprocess.CompletedProcess:
    global LAST_OUTPUT
    proc = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    LAST_OUTPUT = " ".join(argv) + "\n" + proc.stdout + proc.stderr
    return proc


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def theorems_in(path: pathlib.Path) -> list[str]:
    text = strip_comments(path.read_text())
    spaces = NAMESPACE_RE.findall(text)
    if len(spaces) != 1:
        raise SystemExit(f"{path}: expected exactly one namespace, found {spaces}")
    return [f"{spaces[0]}.{name}" for name in THEOREM_RE.findall(text)]


def main() -> int:
    OUT.mkdir(exist_ok=True)
    report: dict = {"lean": run(["lean", "--version"]).stdout.strip(), "modules": {}}

    # Inventory and hashes.
    modules = [("OperatorFirst." + m, ROOT / "OperatorFirst" / f"{m}.lean") for m in LIBRARY]
    modules.append(("OffsetLean.Headline", ROOT / "OffsetLean" / "Headline.lean"))
    names: list[str] = []
    for module, path in modules:
        found = theorems_in(path)
        if not found:
            raise SystemExit(f"no theorems found in {module}")
        report["modules"][module] = {
            "file": str(path.relative_to(ROOT)),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "theorems": len(found),
        }
        names += found
    library_count = sum(v["theorems"] for k, v in report["modules"].items()
                        if k.startswith("OperatorFirst."))
    headline_count = report["modules"]["OffsetLean.Headline"]["theorems"]
    if library_count != EXPECTED_LIBRARY_THEOREMS or headline_count != EXPECTED_HEADLINE_THEOREMS:
        raise SystemExit(f"inventory changed: library {library_count}, headline {headline_count}")
    report["library_theorems"] = library_count
    report["headline_theorems"] = headline_count

    # Axiom audit.
    audit = OUT / "AxiomAudit.lean"
    lines = ["import OperatorFirst", "import OffsetLean", ""]
    lines += [f"#print axioms {name}" for name in names]
    audit.write_text("\n".join(lines) + "\n")
    proc = run(["lake", "env", "lean", str(audit.relative_to(ROOT))])
    log = proc.stdout + proc.stderr
    (OUT / "axioms.log").write_text(log)
    if proc.returncode != 0:
        print(log)
        raise SystemExit("axiom audit file did not compile")
    axioms: dict[str, list[str]] = {}
    for name in names:
        dep = re.search(re.escape(f"'{name}' depends on axioms: [") + r"([^\]]*)\]", log, re.S)
        none = f"'{name}' does not depend on any axioms" in log
        if dep:
            used = sorted(a.strip() for a in dep.group(1).replace("\n", " ").split(",") if a.strip())
        elif none:
            used = []
        else:
            raise SystemExit(f"no axiom report for {name}")
        bad = set(used) - ALLOWED
        if bad:
            raise SystemExit(f"{name} uses disallowed axioms {sorted(bad)}")
        axioms[name] = used
    report["axioms"] = axioms
    report["axiom_union"] = sorted({a for used in axioms.values() for a in used})

    # False controls.
    controls = {}
    for path in sorted((ROOT / "FalseControls").glob("*.lean")):
        proc = run(["lake", "env", "lean", str(path.relative_to(ROOT))])
        text = proc.stdout + proc.stderr
        (OUT / f"{path.stem}.log").write_text(text)
        if proc.returncode == 0:
            print(text)
            raise SystemExit(f"false control ACCEPTED: {path.name}")
        if INFRA_FAILURE.search(text) or not MATH_FAILURE.search(text):
            print(text)
            raise SystemExit(f"false control failed for the wrong reason: {path.name}")
        controls[path.stem] = "rejected"
    if len(controls) < 15:
        raise SystemExit(f"expected 15 false controls, found {len(controls)}")
    report["false_controls"] = controls

    (OUT / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"OK: {library_count} library theorems + {headline_count} headline theorems, "
          f"axioms used: {report['axiom_union']}, {len(controls)} false controls rejected")
    return 0


def annotate(message: str) -> None:
    """Surface a failure as a GitHub error annotation (readable without the log)."""
    flat = message.replace("%", "%25").replace("\r", "").replace("\n", "%0A")
    print(f"::error title=verify.py::{flat[:6000]}")


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit as exc:
        if exc.code not in (0, None):
            annotate(str(exc.code) + "%0A" + LAST_OUTPUT[-5000:])
        raise
