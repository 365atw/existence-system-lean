#!/usr/bin/env python3
"""Write per-item build and axiom logs.

Interface:
  checks/item-logs.sh
      Record every item named in checks/PrintAxioms.lean.
  checks/item-logs.sh KL13
      Record only KL13. Does not rewrite other items' logs.

Both forms run `lake build` once and `lake env lean checks/PrintAxioms.lean`
once. The build log keeps the success line (not linter warnings). The axiom
bar is propext, Classical.choice, and Quot.sound. A declaration that depends
on no axioms is within the bar.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PRINT_AXIOMS = ROOT / "checks" / "PrintAxioms.lean"
LOGS = ROOT / "logs"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SHARED = (LOGS / "lake-build.log", LOGS / "print-axioms.log")


def parse_axiom_line(ln: str):
    none_at = ln.rfind("' does not depend on any axioms")
    none_mark = "' does not depend on any axioms"
    if ln.startswith("'") and none_at != -1 and none_at + len(none_mark) == len(ln):
        return ln[1:none_at], None
    dep_mark = "' depends on axioms: ["
    dep_at = ln.rfind(dep_mark)
    if ln.startswith("'") and ln.endswith("]") and dep_at != -1:
        inner = ln[dep_at + len(dep_mark) : -1]
        axes = [a.strip() for a in inner.split(",") if a.strip()]
        return ln[1:dep_at], axes
    return None


def declarations():
    text = PRINT_AXIOMS.read_text(encoding="utf-8").replace("\r\n", "\n")
    names = re.findall(r"(?m)^#print axioms (\S+)\s*$", text)
    items: list[str] = []
    by_item: dict[str, list[str]] = {}
    for name in names:
        parts = name.split(".")
        if len(parts) < 3 or parts[0] != "ExistenceSystem":
            raise SystemExit(f"unqualified audit line: {name}")
        item = parts[1]
        if item not in by_item:
            items.append(item)
            by_item[item] = []
        by_item[item].append(name)
    if not items:
        raise SystemExit("checks/PrintAxioms.lean has no #print axioms lines")
    return items, by_item


def decode(raw: bytes) -> str:
    for enc in ("utf-8", "utf-8-sig"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            continue
    return raw.decode("cp1252", errors="replace")


def run(cmd: list[str]) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out = decode(proc.stdout).replace("\r\n", "\n")
    err = decode(proc.stderr).replace("\r\n", "\n")
    return proc.returncode, out, err


def build_summary(code: int, out: str, err: str) -> str:
    """Committed build log: the success line, or the full output when the build fails.

    Linter warnings are not item-specific and used to be omitted from the shared
    build log. A successful run keeps that shape.
    """
    if code == 0:
        hits = [ln.strip() for ln in out.splitlines() if "Build completed successfully" in ln]
        if hits:
            return hits[-1]
        lines = [ln.strip() for ln in out.splitlines() if ln.strip()]
        if lines:
            return lines[-1]
        return "Build completed successfully."
    parts = [part.strip() for part in (out, err) if part.strip()]
    return "\n".join(parts)


def write_log(path: Path, body: str, code: int) -> None:
    body = body.replace("\r\n", "\n").rstrip("\n")
    content = (body + "\n" if body else "") + f"exit={code}\n"
    path.write_bytes(content.encode("utf-8"))


def axiom_lines(text: str) -> list[str]:
    return [ln for ln in text.replace("\r\n", "\n").split("\n") if ln.strip() and ln.strip() != "exit=0"]


def preserve_shared_axiom_log(fresh: dict[str, tuple[str, list[str] | None]]) -> None:
    """Drop the shared axiom log only after its declarations are in the fresh audit."""
    old_path = LOGS / "print-axioms.log"
    if not old_path.exists():
        return
    old = axiom_lines(old_path.read_text(encoding="utf-8", errors="replace"))
    old_map = {}
    for ln in old:
        parsed = parse_axiom_line(ln.strip())
        if parsed is None:
            raise SystemExit(f"shared print-axioms.log has an unexpected line: {ln}")
        old_map[parsed[0]] = parsed[1]
    if len(old_map) != len(old):
        raise SystemExit("shared print-axioms.log repeats a declaration; refusing to replace it")
    ascii_old = {name: axes for name, axes in old_map.items() if name.isascii()}
    missing = [name for name in ascii_old if name not in fresh]
    if missing:
        raise SystemExit("fresh audit dropped shared-log declarations: " + ", ".join(missing[:8]))
    for name, axes in ascii_old.items():
        if fresh[name] != axes:
            raise SystemExit(f"axiom set changed for {name}: {axes} -> {fresh[name]}")
    non_ascii = [name for name in old_map if not name.isascii()]
    fresh_non_ascii = [name for name in fresh if not name.isascii()]
    if len(non_ascii) != len(fresh_non_ascii):
        raise SystemExit(
            f"non-ascii declaration count changed: shared log {len(non_ascii)}, fresh {len(fresh_non_ascii)}"
        )
    print(
        f"preserved {len(old_map)} shared axiom declarations "
        f"({len(ascii_old)} ascii names matched, {len(non_ascii)} non-ascii names counted)",
        file=sys.stderr,
    )


def main(argv: list[str]) -> int:
    items, by_item = declarations()
    unknown = [arg for arg in argv if arg not in by_item]
    if unknown:
        raise SystemExit("unknown item: " + ", ".join(unknown))
    selected = argv or items
    record_all = not argv
    LOGS.mkdir(exist_ok=True)

    problems: list[str] = []
    # One package build. Write the summary only into the selected items' logs
    # so a branch that passes its own item does not rewrite the others.
    code, out, err = run(["lake", "build"])
    summary = build_summary(code, out, err)
    for item in selected:
        write_log(LOGS / f"{item}-build.log", summary, code)
    if code != 0:
        problems.append(f"lake build exited {code}")

    code, out, err = run(["lake", "env", "lean", "checks/PrintAxioms.lean"])
    text = out if code == 0 else out + "\n" + err
    if code != 0:
        problems.append(f"axiom audit exited {code}")
    grouped: dict[str, list[str]] = {item: [] for item in selected}
    fresh: dict[str, tuple[str, list[str] | None]] = {}
    for ln in axiom_lines(text):
        parsed = parse_axiom_line(ln.strip())
        if parsed is None:
            problems.append(f"unexpected axiom output: {ln}")
            continue
        name, axes = parsed
        parts = name.split(".")
        if len(parts) < 3 or parts[0] != "ExistenceSystem":
            problems.append(f"unexpected declaration name: {name}")
            continue
        item = parts[1]
        fresh[name] = (name, axes)
        if item in grouped:
            grouped[item].append(ln.strip())
        elif record_all:
            problems.append(f"{name} is not one of the requested items")
        if axes is not None:
            extra = [ax for ax in axes if ax not in ALLOWED]
            if extra:
                problems.append(f"{name} depends on {extra}")

    for item in selected:
        expected = by_item[item]
        got = []
        for ln in grouped[item]:
            parsed = parse_axiom_line(ln)
            if parsed is not None:
                got.append(parsed[0])
        if got != expected:
            problems.append(
                f"{item}: audit output does not match checks/PrintAxioms.lean "
                f"(missing {sorted(set(expected) - set(got))}, extra {sorted(set(got) - set(expected))})"
            )

    axiom_code = 0 if code == 0 and not problems else (code or 1)
    for item in selected:
        body = "\n".join(grouped[item])
        write_log(LOGS / f"{item}-print-axioms.log", body, axiom_code)

    if problems:
        for msg in problems:
            print(msg, file=sys.stderr)
        return 1

    if record_all:
        preserve_shared_axiom_log({name: axes for name, (_name, axes) in fresh.items()})
        for path in SHARED:
            if path.exists():
                path.unlink()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except SystemExit:
        raise
    except subprocess.SubprocessError as exc:
        print(exc, file=sys.stderr)
        raise SystemExit(1)
