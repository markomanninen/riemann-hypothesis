#!/usr/bin/env python3
"""Prepare and lay out the comparison of the propositions from the literature with the theorems they are named after.

Usage: python3 -I verification/reuse/audit.py dossiers
       python3 -I verification/reuse/audit.py collect FOLDER
       python3 -I verification/reuse/audit.py render

Run statements.py of this folder first. It writes data/published_vocabulary.json, which names,
for each proposition from the literature that has a proof and a vocabulary of at most 20
definitions, the definitions of the project that the proposition needs.

dossiers  writes one file for each of those propositions into data/audit/batchNN, ten to a
          folder. A dossier holds the whole Lean text of the proposition and of every
          definition of its vocabulary, with the `variable` lines in scope. Nothing is cut. It
          also writes data/audit/index.json with the order, the names and the folders.

collect   reads the answers of the model runs from FOLDER, where the first reader's answer for a
          batch is A-batchNN.out, the second reader's B-batchNN.out and the check's
          C-batchNN.out, and writes them with the figures of each proposition to audit.json.

render    reads audit.json of this folder, which holds what two readers and a check wrote about
          each dossier, and writes the part of AUDIT.md below the line `<!-- entries -->`. The
          text above that line is kept.

The readings were written by language models from the dossiers, as AUDIT.md describes, so this
script does not make them.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
VERIFICATION = os.path.dirname(HERE)
OUT = os.path.join(HERE, "data", "audit")
MARK = "<!-- entries -->"
BATCH = 10
sys.path.insert(0, os.path.join(VERIFICATION, "explorer"))
import build_statements  # noqa: E402  The statement splitter of the explorer.

# The splitter cuts long texts for the explorer. A dossier keeps them whole.
build_statements.MAX_GIVEN = build_statements.MAX_CLAIM = build_statements.MAX_VALUE = 10 ** 9
# It also drops the value of an instance, which a dossier needs in order to show what the instance is.
build_statements.NO_VALUE = ("theorem", "lemma")


def short(name):
    return name.rsplit(".", 1)[-1]


class Source:
    """The declarations of the source text, by module."""

    def __init__(self):
        self.cache = {}

    def text(self, module, name):
        """The Lean text of one declaration, with the variable lines in scope, or None."""
        if module not in self.cache:
            found = build_statements.statements(module)
            self.cache[module] = (found[0], {d[1]: d for d in found[1]}) if found else ([], {})
        contexts, table = self.cache[module]
        d = table.get(name)
        if d is None:
            return None
        d = list(d) + [""] * (9 - len(d))
        kind, context = d[0], (contexts[d[2] - 1] if d[2] else "")
        code = kind + " " + short(name) + ((" " + d[3]) if d[3] else "") + ((" :\n    " + d[4]) if d[4] else "")
        if d[5]:
            code += " :=\n" + d[5]
        return (context + "\n\n" if context else "") + code

    def unnamed(self, module, compiled):
        """The source text of the instances without a name in a module that Lean can have named
        `compiled`. Lean names such an instance `inst` followed by the class and the heads of
        its arguments, so an instance fits when the name continues with its class."""
        if ("unnamed", module) not in self.cache:
            path = os.path.join(build_statements.REPO, "src", *module.split(".")) + ".lean"
            with open(path, encoding="utf-8") as f:
                text = build_statements.COMMENT.sub("", f.read())
            starts = [m.start() for m in build_statements.COMMAND.finditer(text)] + [len(text)]
            found = []
            for a, b in zip(starts, starts[1:]):
                cmd = text[a:b]
                m = build_statements.HEAD.match(cmd)
                if not m or m.group(2) != "instance":
                    continue
                rest = cmd[m.end():]
                pr = build_statements.PRIORITY.match(rest)
                if pr:
                    rest = rest[pr.end():]
                if build_statements.NAME.match(rest):
                    continue
                claim = build_statements.split("instance", rest)[1]
                head = re.match(r"\s*([\w.]+)", claim)
                found.append((head.group(1).rsplit(".", 1)[-1] if head else "", cmd.strip()))
            self.cache[("unnamed", module)] = found
        rest = compiled.rsplit(".", 1)[-1][len("inst"):]
        return [cmd for head, cmd in self.cache[("unnamed", module)] if head and rest.startswith(head)]


def dossiers():
    with open(os.path.join(HERE, "data", "published_vocabulary.json"), encoding="utf-8") as f:
        vocab = json.load(f)
    with open(os.path.join(HERE, "summary.json"), encoding="utf-8") as f:
        listed = {p["name"]: p for p in json.load(f)["published"]["list"]}
    names = sorted(vocab, key=lambda n: (len(vocab[n]["definitions"]), n))
    source = Source()
    os.makedirs(OUT, exist_ok=True)
    index, missing, unmatched = [], 0, 0
    for k, name in enumerate(names, 1):
        v, p = vocab[name], listed[name]
        folder = f"batch{(k - 1) // BATCH + 1:02d}"
        os.makedirs(os.path.join(OUT, folder), exist_ok=True)
        lines = [f"# Proposition {k}, `{name}`", "",
                 f"The source labels this proposition as a result from the literature. It lies in the module `{v['module']}`.",
                 f"The theorem `{p['proof']}` of the source states it without hypotheses, and the proof of that theorem",
                 f"rests on {p['proof_rests_on']:,} declarations of the project. The proof is not shown here.", "",
                 "## The proposition", ""]
        text = source.text(v["module"], name)
        lines += ["```lean", text or "(the splitter did not find this declaration)", "```", ""]
        missing += text is None
        if v["definitions"]:
            lines += ["## The definitions of the project that the proposition needs", "",
                      f"These are all {len(v['definitions'])} definitions of the project that the proposition mentions, directly or",
                      "through another definition. Every other name in the texts is a constant of Mathlib or Lean.", ""]
            for d in v["definitions"]:
                text = source.text(d["module"], d["name"])
                missing += text is None
                lines += [f"### `{d['name']}`", "", f"{d['kind']} in module `{d['module']}`", "",
                          "```lean", text or "(the splitter did not find this declaration)", "```", ""]
        else:
            lines += ["The proposition mentions no definition of the project. Every name in it is a constant of Mathlib or Lean.", ""]
        if v.get("unnamed_instances"):
            lines += ["## Instances without a name that the proposition needs", "",
                      "The compiled proposition also uses instances that the source declares without a name. Lean names",
                      "such an instance itself, and the text below is every instance without a name of the same module",
                      "whose class fits that name.", ""]
            for d in v["unnamed_instances"]:
                texts = source.unnamed(d["module"], d["name"])
                unmatched += not texts
                lines += [f"### `{d['name']}`", "", f"instance in module `{d['module']}`", ""]
                for text in texts or ["(no instance without a name of this module fits the name)"]:
                    lines += ["```lean", text, "```", ""]
        slug = re.sub(r"[^\w]+", "_", short(name))[:60]
        file = f"{k:02d}-{slug}.md"
        body = "\n".join(lines)
        with open(os.path.join(OUT, folder, file), "w", encoding="utf-8") as f:
            f.write(body)
        index.append({"number": k, "name": name, "folder": folder, "file": file, "vocabulary": len(v["definitions"]),
                      "unnamed_instances": len(v.get("unnamed_instances", [])),
                      "proof": p["proof"], "proof_rests_on": p["proof_rests_on"], "chars": len(body)})
    with open(os.path.join(OUT, "index.json"), "w", encoding="utf-8") as f:
        json.dump(index, f, indent=1, ensure_ascii=False)
    sizes = [r["chars"] for r in index]
    print(f"{len(index)} dossiers in {index[-1]['folder'][-2:]} folders, {sum(sizes):,} characters, largest {max(sizes):,}, "
          f"{missing} declarations not found, {unmatched} instances without a name not matched")


def answers(folder, role):
    """The JSON arrays that one role wrote for the batches, by the number of the proposition."""
    out = {}
    for file in sorted(os.listdir(folder)):
        if re.fullmatch(role + r"-batch\d+\.out", file):
            with open(os.path.join(folder, file), encoding="utf-8") as f:
                text = f.read()
            for entry in json.loads(text[text.index("["):text.rindex("]") + 1]):
                out[int(entry["number"])] = entry
    return out


def collect(folder):
    with open(os.path.join(OUT, "index.json"), encoding="utf-8") as f:
        index = json.load(f)
    a, b, c = answers(folder, "A"), answers(folder, "B"), answers(folder, "C")
    entries = []
    for r in index:
        k = r["number"]
        if k not in a or k not in b or k not in c:
            sys.exit(f"proposition {k} lacks an answer")
        entries.append({"number": k, "name": r["name"], "vocabulary": r["vocabulary"],
                        "unnamed_instances": r["unnamed_instances"], "proof": r["proof"],
                        "proof_rests_on": r["proof_rests_on"],
                        "a": {x: y for x, y in a[k].items() if x not in ("number", "name")},
                        "b": {x: y for x, y in b[k].items() if x != "number"},
                        "check": {x: y for x, y in c[k].items() if x != "number"}})
    with open(os.path.join(HERE, "audit.json"), "w", encoding="utf-8") as f:
        json.dump({"propositions": entries}, f, indent=1, ensure_ascii=False)
    print(f"{len(entries)} propositions written to audit.json")


def clip(text, limit=70):
    """A text for a table cell, cut at a word and with its bars escaped."""
    text = " ".join(str(text).split()).rstrip(".")
    text = text if len(text) <= limit else text[:limit].rsplit(" ", 1)[0] + " …"
    return text.replace("|", "\\|")


def sentence(text):
    text = " ".join(str(text).split())
    return text if text.endswith((".", "!", "?")) else text + "."


RELATION = {"same": "the same statement", "special case": "a special case", "weaker": "a weaker statement",
            "stronger": "a stronger statement", "different": "a different statement", "cannot tell": "undecided"}


def render():
    with open(os.path.join(HERE, "audit.json"), encoding="utf-8") as f:
        entries = json.load(f)["propositions"]
    body = ["## The propositions at a glance", "",
            "| No. | Proposition | Theorem that the name points to | First reader | Second reader | Check | Vocabulary | The proof rests on |",
            "|---:|---|---|---|---|---|---:|---:|"]
    for e in entries:
        body.append(f"| {e['number']} | `{short(e['name'])}` | {clip(e['a']['classical_name'])} | {e['a']['relation']} | "
                    f"{e['b']['relation']} | {e['check']['relation']} | {e['vocabulary']} | {e['proof_rests_on']:,} |")
    body += ["", "## The propositions", ""]
    for e in entries:
        a, b, c = e["a"], e["b"], e["check"]
        body += [f"### {e['number']}, `{short(e['name'])}`", "",
                 f"The proposition is `{e['name']}`. Its vocabulary has {e['vocabulary']} definitions of the project, and the "
                 f"proof of the theorem `{e['proof']}` that states it rests on {e['proof_rests_on']:,} declarations.", "",
                 sentence(a["states"]), "", "```", a["notation"], "```", "",
                 "The theorem that the name points to, as the first reader states it from its own knowledge. "
                 + sentence(a["classical"]), "",
                 f"The first reader takes the proposition for {RELATION.get(a['relation'], a['relation'])} and the second reader for "
                 f"{RELATION.get(b['relation'], b['relation'])}. The check takes it for {RELATION.get(c['relation'], c['relation'])}.", ""]
        if c.get("differences"):
            body += ["The check confirmed these differences from the Lean text.", ""]
            body += [f"- {sentence(d)}" for d in c["differences"]] + [""]
        if c.get("note"):
            body += ["The check gives this reason for its judgement. " + sentence(c["note"]), ""]
        if c.get("vacuity") and c["vacuity"].strip().lower().rstrip(".") != "none found":
            body += ["On emptiness the check wrote this. " + sentence(c["vacuity"]), ""]
        else:
            body += ["The check found no emptiness.", ""]
        errors = c.get("a_errors") or []
        if errors:
            body += ["The check found these errors in the first reader's account of the Lean text, and the account above is "
                     "printed as the reader wrote it.", ""]
            body += [f"- {sentence(x)}" for x in errors] + [""]
        else:
            body += ["The check found no error in the first reader's account of the Lean text.", ""]
        body += [f"The first reader's confidence is {a['confidence']}. {sentence(a['why'])}", ""]
    path = os.path.join(HERE, "AUDIT.md")
    with open(path, encoding="utf-8") as f:
        text = f.read()
    head = text[:text.index(MARK) + len(MARK)] if MARK in text else text.rstrip() + "\n\n" + MARK
    with open(path, "w", encoding="utf-8") as f:
        f.write(head + "\n\n" + "\n".join(body).rstrip() + "\n")
    print(f"{len(entries)} propositions written to AUDIT.md")


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "collect":
        collect(sys.argv[2])
    elif len(sys.argv) == 2 and sys.argv[1] in ("dossiers", "render"):
        {"dossiers": dossiers, "render": render}[sys.argv[1]]()
    else:
        sys.exit(__doc__)
