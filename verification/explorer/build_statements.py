#!/usr/bin/env python3
"""Collect the statements of every module, for the statement list of the explorer.

Usage: python3 -I verification/explorer/build_statements.py [MODULE ...]

Run build_data.py first. This script reads its module order from data/names.json, reads every
source file and writes into data/:

  stmtN.gz.txt      the statements of 500 modules, as JSON, gzipped and written as base64 text
  statements.json   the chunk size, the counts and the three length limits

With module names as arguments it prints the statements of those modules and writes nothing.

A statement is the text of a declaration without its proof. For a theorem that is the part
before the first `:=` outside brackets, split at the first colon outside brackets into what is
given and what is claimed. A definition keeps its value, and a structure keeps its fields. The
`variable` lines in scope are kept with each statement, because Lean adds those variables to a
statement that uses them. The split works on the text and does not run Lean.

One module is [contexts, declarations]. A context is the `variable`, `include`, `omit` and
notation lines in scope, joined by newlines. A declaration is
[kind, full name, context index + 1 or 0, given, claim, value, and the number of characters
left out of the given, the claim and the value], with empty entries at the end left out.
"""
import base64
import gzip
import json
import multiprocessing
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
DATA = os.path.join(HERE, "data")
CHUNK = 500
MAX_GIVEN, MAX_CLAIM, MAX_VALUE = 3000, 3000, 2000

COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)
# A command starts on a line that begins with one of these words at the left edge. A statement
# may continue on a line at the left edge, so the edge alone does not end it.
COMMAND = re.compile(r"^(?=@\[|#\w|(?:import|theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque"
                     r"|axiom|example|open|end|namespace|section|variable|universe|noncomputable|private|protected"
                     r"|public|nonrec|unsafe|partial|set_option|attribute|omit|include|local|scoped|macro"
                     r"|macro_rules|syntax|notation|infix|infixl|infixr|prefix|postfix|elab|elab_rules|mutual"
                     r"|export|alias|initialize|run_cmd|declare_syntax_cat|add_decl_doc|suppress_compilation"
                     r"|unseal|seal|meta|module)\b)", re.M)
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
SECTION = re.compile(ATTRS + r"(?:(?:noncomputable|public|private|meta|protected)\s+)*(?:section|mutual)\b")
PREFIX = re.compile(r"(omit|include|variable|open|set_option|attribute)\b[^\n]*?\s+in\s*(?:\n|$)")
NOTATION = re.compile(r"(?:(?:local|scoped)\s+)?(?:notation|infixl?|infixr|prefix|postfix)\b")
HEAD = re.compile(ATTRS + r"((?:(?:private|protected|noncomputable|nonrec|unsafe|partial|public|scoped|local)\s+)*)"
                  r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\b[ \t]*")
PRIORITY = re.compile(r"\(priority[^)]*\)\s*")
NAME = re.compile(r"((?:[^\s:({\[⦃«]|«[^»]*»)+?)(\.\{[^}]*\})?(?=[\s:({\[⦃]|$)")
TOKEN = re.compile(r"[(\[{⟨⦃]|[)\]}⟩⦄]|:=|::|:|\bwhere\b|\n[ \t]*\|")
LET = re.compile(r"\b(?:letI|haveI|let|have)\b[^;\n]*$")
OPENERS, CLOSERS = "([{⟨⦃", ")]}⟩⦄"
NO_VALUE = ("theorem", "lemma", "instance")
BRANCHING = ("inductive", "structure", "class")


def tidy(text):
    """Strip the text and remove the indentation that its later lines share."""
    lines = [l.rstrip() for l in text.strip().split("\n")]
    rest = [l for l in lines[1:] if l]
    cut = min((len(l) - len(l.lstrip()) for l in rest), default=0)
    return "\n".join([lines[0]] + [l[cut:] for l in lines[1:]])


def split(kind, sig):
    """Split the text after a declaration's name into given, claim and value."""
    depth, colon, end, how = 0, -1, -1, ""
    for t in TOKEN.finditer(sig):
        s = t.group()
        if s in OPENERS:
            depth += 1
        elif s in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0:
            if s == ":":
                if colon < 0:
                    colon = t.start()
            elif s == ":=":
                # `let x := v; ...` and `letI := inst; ...` inside a claim are part of the claim.
                if LET.search(sig, max(sig.rfind(";", 0, t.start()), sig.rfind("\n", 0, t.start())) + 1, t.start()):
                    continue
                end, how = t.start(), s
                break
            elif s == "where":
                end, how = t.start(), s
                break
            elif s[0] == "\n":
                # A line that starts with a bar begins the cases of a definition by cases. A claim
                # can also start with the bar of an absolute value, so a bar right after the
                # colon stays in the claim, and so does a bar whose arrow sits inside brackets.
                if colon >= 0 and not sig[colon + 1:t.start()].strip():
                    continue
                line_end = sig.find("\n", t.end())
                line = sig[t.end():line_end if line_end >= 0 else len(sig)]
                arrow = line.find("=>")
                head = line[:arrow]
                if kind in BRANCHING or (arrow >= 0 and all(head.count(o) == head.count(c) for o, c in zip(OPENERS, CLOSERS))):
                    end, how = t.start(), "|"
                    break
    stop = end if end >= 0 else len(sig)
    if colon >= 0:
        given, claim = sig[:colon], sig[colon + 1:stop]
    else:
        given, claim = sig[:stop], ""
    value = ""
    if end >= 0 and kind not in NO_VALUE:
        value = sig[end if how == "|" else end + len(how):]
    return tidy(given), tidy(claim), tidy(value)


def statements(module):
    """The contexts and declarations of one module."""
    path = os.path.join(REPO, "src", *module.split(".")) + ".lean"
    with open(path, encoding="utf-8") as f:
        text = COMMENT.sub("", f.read())
    starts = [m.start() for m in COMMAND.finditer(text)] + [len(text)]
    scopes = [{"ns": "", "lines": []}]
    pending, contexts, table, out = [], [], {}, []
    for a, b in zip(starts, starts[1:]):
        cmd = text[a:b]
        while True:
            # `omit [inst] in`, `include h in` and the like stand before the declaration they apply to.
            p = PREFIX.match(cmd)
            if not p:
                break
            if p.group(1) in ("omit", "include", "variable"):
                pending.append(" ".join(p.group().split()))
            cmd = cmd[p.end():]
        if not cmd.strip():
            continue
        word = cmd.split(None, 1)[0]
        if word == "namespace":
            scopes.append({"ns": cmd.split()[1], "lines": []})
        elif word == "end":
            if len(scopes) > 1:
                scopes.pop()
        elif SECTION.match(cmd):
            scopes.append({"ns": "", "lines": []})
        elif word in ("variable", "include", "omit") or NOTATION.match(cmd):
            scopes[-1]["lines"].append(" ".join(cmd.split()))
        else:
            m = HEAD.match(cmd)
            if not m:
                continue
            kind = m.group(2)
            rest = cmd[m.end():]
            pr = PRIORITY.match(rest)
            if pr:
                rest = rest[pr.end():]
            nm = NAME.match(rest)
            name = nm.group(1) if nm else ""
            sig = rest[nm.end():] if nm else rest
            given, claim, value = split(kind, sig)
            if name.startswith("_root_."):
                name = name[7:]
            elif name:
                name = ".".join([s["ns"] for s in scopes if s["ns"]] + [name])
            ctx = "\n".join([l for s in scopes for l in s["lines"]] + pending)
            pending = []
            if ctx and ctx not in table:
                contexts.append(ctx)
                table[ctx] = len(contexts)
            row = [" ".join((m.group(1) + kind).split()), name, table.get(ctx, 0), given[:MAX_GIVEN],
                   claim[:MAX_CLAIM], value[:MAX_VALUE], max(0, len(given) - MAX_GIVEN),
                   max(0, len(claim) - MAX_CLAIM), max(0, len(value) - MAX_VALUE)]
            while row and not row[-1]:
                row.pop()
            out.append(row)
    return [contexts, out] if out else 0


def work(job):
    index, modules = job
    rows = [statements(m) for m in modules]
    raw = json.dumps(rows, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    packed = base64.b64encode(gzip.compress(raw, 9, mtime=0))
    with open(os.path.join(DATA, f"stmt{index}.gz.txt"), "wb") as f:
        f.write(packed)
    decls = [d for r in rows if r for d in r[1]]
    kinds = {}
    for d in decls:
        k = d[0].split()[-1]
        kinds[k] = kinds.get(k, 0) + 1
    return {"raw": len(raw), "packed": len(packed), "kinds": kinds,
            "empty": sum(1 for r in rows if not r),
            "cut_given": sum(1 for d in decls if len(d) > 6 and d[6]),
            "cut_claim": sum(1 for d in decls if len(d) > 7 and d[7]),
            "cut_values": sum(1 for d in decls if len(d) > 8 and d[8]),
            "no_claim": sum(1 for d in decls if d[0].split()[-1] in ("theorem", "lemma") and (len(d) < 5 or not d[4]))}


def main():
    if len(sys.argv) > 1:
        for module in sys.argv[1:]:
            print(json.dumps(statements(module), ensure_ascii=False, indent=1))
        return
    with open(os.path.join(DATA, "names.json"), encoding="utf-8") as f:
        coded = json.load(f)
    names, prev = [], ""
    for k, rest in coded:
        prev = prev[:k] + rest
        names.append(prev)
    jobs = [(i // CHUNK, names[i:i + CHUNK]) for i in range(0, len(names), CHUNK)]
    total = {"raw": 0, "packed": 0, "empty": 0, "cut_given": 0, "cut_claim": 0, "cut_values": 0, "no_claim": 0}
    kinds, largest = {}, 0
    with multiprocessing.Pool() as pool:
        for done, r in enumerate(pool.imap_unordered(work, jobs), 1):
            for k in total:
                total[k] += r[k]
            for k, v in r["kinds"].items():
                kinds[k] = kinds.get(k, 0) + v
            largest = max(largest, r["packed"])
            sys.stderr.write(f"\rchunk {done} of {len(jobs)}")
    sys.stderr.write("\n")
    meta = {"chunk": CHUNK, "chunks": len(jobs), "modules": len(names), "declarations": sum(kinds.values()),
            "kinds": dict(sorted(kinds.items(), key=lambda t: -t[1])), "modulesWithoutDeclarations": total["empty"],
            "maxGiven": MAX_GIVEN, "maxClaim": MAX_CLAIM, "maxValue": MAX_VALUE,
            "cutGiven": total["cut_given"], "cutClaim": total["cut_claim"], "cutValues": total["cut_values"],
            "theoremsWithoutClaim": total["no_claim"],
            "bytes": total["raw"], "packedBytes": total["packed"], "largestFile": largest}
    with open(os.path.join(DATA, "statements.json"), "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps(meta, indent=1))


if __name__ == "__main__":
    main()
