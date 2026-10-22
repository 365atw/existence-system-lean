#!/usr/bin/env bash
# Observable contract: union merge on the two shared Lean files, per-item logs.
# Independent of checks/item_logs.py. Exit non-zero when the contract is absent.
set -eu
cd "$(dirname "$0")/.."

# The Windows Store python3 alias exists but does not run. Probe for a real interpreter.
if python3 -c 'import sys; raise SystemExit(0 if sys.version_info[0] == 3 else 1)' >/dev/null 2>&1; then
  set -- python3
elif python -c 'import sys; raise SystemExit(0 if sys.version_info[0] == 3 else 1)' >/dev/null 2>&1; then
  set -- python
elif py -3 -c 'import sys; raise SystemExit(0 if sys.version_info[0] == 3 else 1)' >/dev/null 2>&1; then
  set -- py -3
else
  echo "FAIL: python is required to read the log contract" >&2
  exit 1
fi

exec "$@" - <<'PY'
import pathlib, re, sys

root = pathlib.Path(".")
fail = []

def check(cond, msg):
    if not cond:
        fail.append(msg)

def parse_axiom_line(ln):
    """Return (name, axes or None). Axes is None when the declaration uses no axioms.

    Declaration names may contain a prime, so the closing quote is the one
    before the fixed #print axioms phrase, not the first quote in the name.
    """
    none_at = ln.rfind("' does not depend on any axioms")
    if ln.startswith("'") and none_at != -1 and none_at + len("' does not depend on any axioms") == len(ln):
        return ln[1:none_at], None
    dep_at = ln.rfind("' depends on axioms: [")
    if ln.startswith("'") and ln.endswith("]") and dep_at != -1:
        inner = ln[dep_at + len("' depends on axioms: ["):-1]
        axes = [a.strip() for a in inner.split(",") if a.strip()]
        return ln[1:dep_at], axes
    return None

attr_path = root / ".gitattributes"
raw_attr = attr_path.read_bytes() if attr_path.is_file() else b""
text = raw_attr.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
expected = (
    b"ExistenceSystem.lean merge=union\n"
    b"checks/PrintAxioms.lean merge=union\n"
)
check(text == expected, ".gitattributes must be exactly the two union-merge lines")

check(not (root / "logs/lake-build.log").exists(), "shared logs/lake-build.log is still present")
check(not (root / "logs/print-axioms.log").exists(), "shared logs/print-axioms.log is still present")
check((root / "logs/README").is_file(), "logs/README is missing")

src_path = root / "checks/PrintAxioms.lean"
src = src_path.read_text(encoding="utf-8") if src_path.is_file() else ""
src_n = src.replace("\r\n", "\n")
unqual = re.findall(r"(?m)^#print axioms (?!ExistenceSystem\.)\S+", src_n)
check(unqual == [], "PrintAxioms.lean still has unqualified #print axioms lines")
opens = re.findall(r"(?m)^open ", src_n)
check(opens == [], "PrintAxioms.lean still uses open, which union merge can reorder")
names = re.findall(r"(?m)^#print axioms (\S+)\s*$", src_n)
qualified = [n for n in names if n.startswith("ExistenceSystem.") and n.count(".") >= 2]
check(len(qualified) == len(names) and len(names) > 0, "every #print axioms line must be ExistenceSystem.<Item>.<decl>")

items = []
for n in qualified:
    item = n.split(".")[1]
    if item not in items:
        items.append(item)

allowed = {"propext", "Classical.choice", "Quot.sound"}
seen = {}
for item in items:
    plog = root / f"logs/{item}-print-axioms.log"
    blog = root / f"logs/{item}-build.log"
    check(plog.is_file(), f"missing {plog.as_posix()}")
    check(blog.is_file(), f"missing {blog.as_posix()}")
    if plog.is_file():
        lines = [ln for ln in plog.read_text(encoding="utf-8").replace("\r\n", "\n").split("\n") if ln.strip()]
        check(bool(lines) and lines[-1] == "exit=0", f"{plog.as_posix()} does not end with exit=0")
        for ln in lines[:-1]:
            parsed = parse_axiom_line(ln)
            if parsed is None:
                fail.append(f"unexpected line in {plog.as_posix()}: {ln}")
                continue
            name, axes = parsed
            if axes is not None:
                extra = [a for a in axes if a not in allowed]
                check(extra == [], f"{name} depends on {extra}")
            seen[name] = item
    if blog.is_file():
        blines = [ln for ln in blog.read_text(encoding="utf-8").replace("\r\n", "\n").split("\n") if ln.strip()]
        check(bool(blines) and blines[-1] == "exit=0", f"{blog.as_posix()} does not end with exit=0")

for n in qualified:
    item = n.split(".")[1]
    check(seen.get(n) == item, f"{n} is missing from logs/{item}-print-axioms.log")

for n, item in seen.items():
    check(n in qualified, f"{n} is in logs/{item}-print-axioms.log but not in PrintAxioms.lean")

readme = (root / "logs/README").read_text(encoding="utf-8") if (root / "logs/README").is_file() else ""
check("logs/<Item>-build.log" in readme and "logs/<Item>-print-axioms.log" in readme,
      "logs/README does not state the per-item log names")

if fail:
    print("FAIL")
    for msg in fail:
        print(f" - {msg}")
    sys.exit(1)
print(f"OK items={','.join(items)} declarations={len(qualified)}")
PY
