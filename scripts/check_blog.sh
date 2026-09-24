#!/usr/bin/env bash
# Blog check: every ```lean block in docs/blog/leanapi.md is checked as the
# `<!-- check: … -->` line directly above it says:
#
#   excerpt <path>      the block appears verbatim (up to whitespace) in <path>
#   signature <name>    the block is a `theorem`/`def` statement without a body,
#                       and its type is exactly that of declaration <name>
#   compile             the block builds, in its own namespace
#
# The imports and `open`s for signature and compile blocks come from the
# `blog-check prelude` comment at the top of the post. A ```lean block without
# a marker is an error: every example must be checked.
#
#   ./scripts/check_blog.sh            check (exit 1 on any failure)
#   ./scripts/check_blog.sh --verbose  also print Lean's output per failing block
set -euo pipefail
cd "$(dirname "$0")/.."
post=docs/blog/leanapi.md
verbose=${1:-}
work=$(mktemp -d -t blogcheck)
python3 - "$post" "$work" <<'PY'
import json, re, sys
post, work = sys.argv[1:3]
text = open(post).read()
m = re.search(r"<!--\s*\nblog-check prelude\n(.*?)-->", text, re.S)
prelude = m.group(1).strip() if m else ""
lines = text.split("\n")
blocks, marker, i = [], None, 0
while i < len(lines):
    ln = lines[i]
    mk = re.match(r"\s*<!--\s*check:\s*(.*?)\s*-->\s*$", ln)
    if mk:
        marker = mk.group(1); i += 1; continue
    if ln.strip() == "```lean":
        j = i + 1
        while lines[j].strip() != "```": j += 1
        blocks.append({"line": i + 1, "marker": marker, "src": "\n".join(lines[i + 1:j])})
        marker = None; i = j + 1; continue
    if ln.strip(): marker = None if not ln.startswith("<!--") else marker
    i += 1

def header_to_example(src, name):
    s = re.sub(r"/--.*?-/", "", src, flags=re.S).strip()
    m = re.match(r"(?:theorem|def|abbrev|lemma)\s+\S+", s)
    if not m: return None
    rest, k, binders = s[m.end():], 0, []
    opens, closes = "([{⦃", ")]}⦄"
    while True:
        while k < len(rest) and rest[k].isspace(): k += 1
        if k < len(rest) and rest[k] in opens:
            depth, j = 0, k
            while True:
                c = rest[j]
                if c in opens: depth += 1
                elif c in closes:
                    depth -= 1
                    if depth == 0: break
                j += 1
            binders.append(rest[k:j + 1]); k = j + 1
        else: break
    if k >= len(rest) or rest[k] != ":": return None
    # The block has no body, so the rest is the whole type. It may contain
    # `:=` of its own (`let (a, s) := …` in a statement).
    ty = rest[k + 1:].strip()
    stmt = f"∀ {' '.join(binders)}, ({ty})" if binders else ty
    tries = " | ".join(f"exact @{name}" + " _" * n for n in range(4))
    return f"example : {stmt} := by\n  first | {tries}"

norm = lambda s: re.sub(r"\s+", " ", s).strip()
lean, results = [prelude, ""], []
for n, b in enumerate(blocks):
    mk = b["marker"]
    if not mk:
        results.append((b["line"], "unmarked", False, "no <!-- check: … --> marker")); continue
    kind, _, arg = mk.partition(" ")
    if kind == "excerpt":
        try:
            ok = norm(b["src"]) in norm(open(arg).read())
            results.append((b["line"], mk, ok, "" if ok else f"not found in {arg}"))
        except FileNotFoundError:
            results.append((b["line"], mk, False, f"{arg} does not exist"))
    elif kind in ("signature", "compile"):
        body = header_to_example(b["src"], arg) if kind == "signature" else b["src"]
        if body is None:
            results.append((b["line"], mk, False, "could not read the statement")); continue
        start = len("\n".join(lean).split("\n")) + 1
        lean += [f"namespace BlogCheck.B{n}", body, f"end BlogCheck.B{n}", ""]
        end = len("\n".join(lean).split("\n"))
        results.append((b["line"], mk, None, (start, end)))
    else:
        results.append((b["line"], mk, False, f"unknown check kind `{kind}`"))
open(f"{work}/Blog.lean", "w").write("\n".join(lean))
json.dump({"prelude_lines": len(prelude.split("\n")), "results": results}, open(f"{work}/results.json", "w"))
PY
lean_out=$(lake env lean "$work/Blog.lean" 2>&1 || true)
echo "$lean_out" > "$work/lean.txt"
python3 - "$work" "$verbose" <<'PY'
import json, re, sys
work, verbose = sys.argv[1], sys.argv[2] == "--verbose"
data = json.load(open(f"{work}/results.json"))
results, prelude_lines = data["results"], data["prelude_lines"]
out = open(f"{work}/lean.txt").read()
err_lines = [int(m.group(1)) for m in re.finditer(r"Blog\.lean:(\d+):\d+: error", out)]
prelude_broken = any(l <= prelude_lines for l in err_lines) or "unknown module prefix" in out \
    or re.search(r"object file .* does not exist", out) is not None
passed = failed = 0
for line, marker, ok, info in results:
    if ok is None:
        start, end = info
        errs = [l for l in err_lines if start <= l <= end]
        ok = not errs and not prelude_broken
        info = "" if ok else ("the prelude's imports do not build" if prelude_broken else f"Lean errors at Blog.lean lines {errs}")
    if ok: passed += 1
    else: failed += 1
    print(f"  {'✓' if ok else '✗'} post line {line}: {marker}" + ("" if ok else f" — {info}"))
if verbose and failed: print("\nLean output:\n" + out)
print(f"blog check: {passed} passed, {failed} failed")
sys.exit(1 if failed else 0)
PY
