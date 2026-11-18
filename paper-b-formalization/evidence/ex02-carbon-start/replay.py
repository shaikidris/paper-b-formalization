"""Rebuild the Paper B starting modules and the source-exact legacy path lemmas."""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
BOARD = HERE.parents[1]
PACKAGE = BOARD / "release-core"
LEGACY = BOARD.parent / "formalization/Controller/Graphs/FailureBatch.lean"
LEGACY_SLICE = "f72dfe57ca64ebba26dd9188ae1610c390f27a88b2f9721d9667ecc63c7848f6"


def run(cwd: Path, *argv: str, local_imports: bool = False, axiom_file: Path | None = None) -> None:
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    if local_imports:
        env["LEAN_PATH"] = str(cwd)
    print("$", " ".join(argv), flush=True)
    if axiom_file is None:
        subprocess.run(argv, cwd=cwd, env=env, check=True)
        return
    output = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True)
    print(output.stdout + output.stderr, end="")
    output.check_returncode()
    controls = [line.split()[-1] for line in axiom_file.read_text().splitlines() if line.startswith("#print axioms ")]
    if not controls:
        raise ValueError("No declarations were selected for the axiom audit")
    lines = set(output.stdout.splitlines())
    for name in controls:
        if f"'{name}' does not depend on any axioms" not in lines:
            raise ValueError(f"Missing axiom-free audit line for {name}")


def replay_legacy(cwd: Path, pin: str) -> None:
    text = LEGACY.read_text()
    start = text.index("namespace Controller.Graphs\n")
    end = text.index("end ReachAvoid", start) + len("end ReachAvoid")
    excerpt = text[start:end]
    if hashlib.sha256(excerpt.encode()).hexdigest() != LEGACY_SLICE:
        raise ValueError("The selected legacy proof declarations have changed")
    (cwd / "LegacyReachExcerpt.lean").write_text(
        "import Std\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n\n"
        + excerpt + "\n\nend FailureDAG\nend Controller.Graphs\n"
    )
    claims = ["source_alive", "target_alive", "mono"]
    (cwd / "LegacyAudit.lean").write_text(
        "import LegacyReachExcerpt\n"
        + "".join(f"#print axioms Controller.Graphs.FailureDAG.ReachAvoid.{x}\n" for x in claims)
    )
    run(cwd, "elan", "run", pin, "lean", "-o", "LegacyReachExcerpt.olean", "LegacyReachExcerpt.lean")
    run(cwd, "elan", "run", pin, "lean", "LegacyAudit.lean", local_imports=True, axiom_file=cwd / "LegacyAudit.lean")


def main() -> None:
    pin = (PACKAGE / "lean-toolchain").read_text().strip()
    with tempfile.TemporaryDirectory(prefix="paper-b-ex02-replay-") as scratch:
        root = Path(scratch)
        source = root / "release-core"
        shutil.copytree(PACKAGE, source, ignore=shutil.ignore_patterns(".lake", ".git", "*.olean", "*.ilean"))
        shutil.copyfile(HERE / "Audit.lean", source / "Audit.lean")
        run(source, "elan", "run", pin, "lean", "--version")
        run(source, "elan", "run", pin, "lake", "build")
        run(source, "elan", "run", pin, "lake", "env", "lean", "Audit.lean", axiom_file=source / "Audit.lean")
        for name in ("Challenge", "PaperB.Spec", "PaperB.ExitPaths"):
            run(source, "elan", "run", pin, "lake", "env", "leanchecker", "--verbose", name)
        replay_legacy(root, pin)


if __name__ == "__main__":
    main()
