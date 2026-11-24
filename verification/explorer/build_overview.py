#!/usr/bin/env python3
"""Write the overview page, from which every part of the verification work opens.

Usage: python3 -I verification/explorer/build_overview.py

The script reads the JSON files that the scripts of the verification folders write and lays
their figures out as overview/index.html. The page says what the proof claims, what has been
checked and by whom, where each part of the work can be read, and what is open. It computes
nothing itself, so run the script of a folder first when its figures changed.

overview/open.json holds the open items that no JSON file states. Each has a text and the date
on which it was written down, and the page prints them after the open items that the readings
themselves record.
"""
import collections
import datetime
import html
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DOCS = "https://github.com/markomanninen/riemann-hypothesis/blob/main/verification/"
REPO = "https://github.com/markomanninen/riemann-hypothesis"

THEOREMS = [
    ("riemannHypothesis", "Mathlib's statement of the Riemann Hypothesis"),
    ("riemannZeta_eq_zero_re", "the same statement, written out"),
    ("LFunction_ne_zero_of_half_lt_re", "L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, "
                                        "except the trivial character at s = 1"),
    ("LFunction_eq_zero_re", "every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2"),
    ("LFunction_eq_zero_re_of_isPrimitive", "the same, for primitive characters"),
]


def load(*parts):
    with open(os.path.join(ROOT, *parts), encoding="utf-8") as f:
        return json.load(f)


def n(x):
    return f"{x:,}"


def esc(x):
    return html.escape(str(x), quote=True)


def count(k, one, many):
    return f"one {one}" if k == 1 else f"{k} {many}"


def card(href, title, text, figure, unit, outside=True):
    target = ' target="_blank" rel="noopener"' if outside else ""
    return (f'<a class="card" href="{esc(href)}"{target}><span class="t">{esc(title)}</span>'
            f'<span class="f"><b>{esc(figure)}</b> {esc(unit)}</span><span class="p">{esc(text)}</span>'
            f'<span class="go">{"Read on GitHub" if outside else "Open"}</span></a>')


def main():
    summary, exact = load("skeleton", "summary.json"), load("skeleton", "exact-tree.json")
    reading, extra = load("skeleton", "reading.json"), load("skeleton", "reading-exact.json")
    published, clean = load("skeleton", "published.json")["summary"], load("skeleton", "clean.json")
    glossary, d7 = load("skeleton", "glossary.json"), load("skeleton", "d7.json")
    unused, axioms = load("decl-graph", "unused.json"), load("decl-graph", "exact-axioms.json")
    true_defs, meta = load("redundancy", "true-predicates.json"), load("explorer", "data", "meta.json")
    with open(os.path.join(HERE, "overview", "open.json"), encoding="utf-8") as f:
        noted = json.load(f)

    lines = reading["lines"] + extra["lines"]
    confidence = collections.Counter(r["confidence"] for r in lines)
    crossed = [r["cross_check"] for r in reading["lines"] if r.get("cross_check")]
    deeper = [r["deeper"] for r in reading["lines"] if r.get("deeper")]
    deep_checks = [d["cross_check"] for d in deeper if d.get("cross_check")]
    deep_changed = [c for c in deep_checks if c["changes"]]
    deep_passed = sum(1 for c in deep_changed if c.get("recheck_errors") == 0)
    deep_fixed = [r["line"] for r in reading["lines"] if r.get("deeper", {}).get("cross_check", {}).get("recheck_errors")]
    names = sorted(axioms["axioms"])

    stats = [(n(meta["modules"]), "modules of Lean source"), (n(meta["lines"]), "lines in them"),
             (n(unused["rows"]), "declarations"), (n(unused["used_rows"]), "of them used by the five theorems")]
    claims = "".join(f"<li><code>{esc(a)}</code><span>{esc(b[0].upper() + b[1:])}.</span></li>" for a, b in THEOREMS)

    checked = [
        ("Axioms", f"A script read the compiled project constant by constant and followed every constant that the five theorems "
                   f"use, {n(axioms['constants_reached'])} in all. The only axioms among them are "
                   f"{', '.join(f'<code>{esc(x)}</code>' for x in names[:-1])} and <code>{esc(names[-1])}</code>, "
                   "the three that Lean's own library uses."),
        ("Kernel replay", "Comparator is the tool that replays a proof in Lean's kernel and in a second, independent checker. "
                          "The notes of the people who check the submission do not yet record a result of its run."),
        ("Readings", f"A language model, Claude, wrote what each of the {len(lines)} largest steps states, and further runs of the "
                     f"same model checked every reading against the Lean text. A model of another maker, Gemini, then read the "
                     f"readings again. Its findings changed {sum(c['changes'] for c in crossed)} passages in "
                     f"{len(crossed)} readings and {sum(c['changes'] for c in deep_changed)} passages in the "
                     f"{len(deep_changed)} deeper readings. None of the findings that held was a sentence that the Lean text "
                     "contradicts."),
        ("After the corrections", f"A further check passed {deep_passed} of the {len(deep_changed)} corrected deeper readings and "
                                  f"found {count(len(deep_fixed), 'error', 'errors')} in the others, which were corrected."),
        ("Mathematics", "No mathematician has checked the readings or the account of the strategy. Both say what the Lean text "
                        "states. Whether a statement labelled as published agrees with the literature is a separate question, "
                        "and nobody has compared them."),
    ]
    checked_html = "".join(f'<div class="item"><h3>{esc(a)}</h3><p>{b}</p></div>' for a, b in checked)

    cards = [
        card("../index.html", "Proof explorer", "The proof as a landscape of modules, the outline of its largest steps with "
             "their readings, and every module with its statements.", n(meta["modules"]), "modules", outside=False),
        card(DOCS + "strategy/README.md", "Strategy of the proof", "The route from the five theorems down to the two bounds "
             "on one lattice, followed through the Lean text.", "9", "steps"),
        card(DOCS + "skeleton/READING.md", "Readings of the outline", f"What each of the largest steps states, premise by "
             f"premise, with the confidence of its reader. {confidence['high']} high, {confidence['medium']} medium and "
             f"{confidence['low']} low.", str(len(lines)), "steps read"),
        card(DOCS + "skeleton/PUBLISHED.md", "Statements labelled as published", "The statements that the code labels as "
             f"published results. The five theorems reach {published['reached']} of them.", n(published["statements"]), "statements"),
        card(DOCS + "skeleton/GLOSSARY.md", "Glossary", "The definitions that the readings leave unopened most often, each "
             "read part by part.", str(len(glossary["entries"])), "definitions"),
        card(DOCS + "skeleton/D7.md", "The record D7", "The record of data that the middle of the proof is built over, with a "
             f"reading of each of the {n(len(d7['definitions']))} definitions below it.", str(d7["whole"]["fields"]), "fields"),
        card(DOCS + "skeleton/README.md", "Skeleton of the argument", "How the largest steps were found. A step gathers the "
             "declarations that the five theorems use only by way of it.", n(exact["skeleton"]["nodes"]),
             "steps that gather 1,000 or more"),
        card(DOCS + "decl-graph/README.md", "Declarations that the proof does not use", "The declaration graph of the "
             "compiled project and the part of it that the five theorems never reach.", n(unused["unused_rows"]),
             "unused declarations"),
        card(DOCS + "redundancy/README.md", "Repeated statements", "Theorems that Lean found to state exactly what another "
             f"theorem states, and {true_defs['definitions_that_are_always_true']} definitions that are always true.",
             n(clean["theorems_left_out"]), "repeating theorems"),
        card(DOCS + "change-check/README.md", "Check of a change", "A tool that says what a change of the source does to "
             "the five theorems before it is merged.", "5", "theorems guarded"),
        card(DOCS + "NOTES.md", "Verification notes", "The source archive, its size, the tools and the sandbox of the "
             "people who check the submission.", "1", "document"),
        card(REPO, "Source", "The Lean source with every document above, as a fork of the repository of the checking group.",
             n(meta["modules"]), "modules"),
    ]

    derived = []
    if deep_fixed:
        derived.append(f"The deeper readings of lines {' and '.join(map(str, deep_fixed))} were corrected after the last check "
                       "and have not been checked since.")
    derived.append("Gemini has read the first versions of the readings and has not read the corrected texts.")
    derived.append("No mathematician has compared a statement labelled as published with its source in the literature.")
    open_html = "".join(f"<li>{esc(x)}</li>" for x in derived)
    open_html += "".join(f"<li>{esc(x['text'])} <span class=\"mute\">Noted on {esc(x['date'])}.</span></li>" for x in noted)

    page = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Overview of the verification work</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Literata:opsz,wght@7..72,400;7..72,600&display=swap" rel="stylesheet">
<style>
/* The page shares the voice, colours and type of the explorer next to it. */
:root{{color-scheme:light dark;--bg:light-dark(#fff,#0f1217);--ink:light-dark(#10131a,#e7e9ee);--mute:light-dark(#5a6170,#9aa1b0);
--rule:light-dark(#dfe3ea,#262b35);--pr:light-dark(#0b4f8a,#7fb2e5);--prs:light-dark(#e6eef7,#16253a);--panel:light-dark(#f6f8fb,#151a22)}}
*{{box-sizing:border-box;min-width:0}}
body{{margin:0;background:var(--bg);color:var(--ink);font:16px/1.55 Literata,Georgia,serif;overflow-x:clip}}
.band{{padding:0 max(4vw,16px);max-width:1100px;margin:0 auto}}
header.band{{padding-top:clamp(18px,3vw,36px)}}
h1{{font-size:clamp(26px,4.2vw,40px);line-height:1.08;margin:0 0 10px;font-weight:600;text-wrap:balance}}
h2{{font-size:22px;margin:36px 0 10px;font-weight:600;border-top:3px solid var(--pr);padding-top:12px}}
h3{{font-size:16px;margin:0 0 2px;font-weight:600}}
p{{margin:0 0 10px;max-width:70ch}}.mute{{color:var(--mute)}}
a{{color:var(--pr)}}
code{{font-family:ui-monospace,Menlo,monospace;font-size:.85em;overflow-wrap:anywhere}}
.stats{{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin:14px 0}}
.stat{{background:var(--panel);border-radius:8px;padding:12px}}
.stat b{{display:block;font-size:24px;font-weight:600;font-variant-numeric:tabular-nums}}
.stat span{{font-size:13px;color:var(--mute)}}
.claims{{list-style:none;padding:0;margin:0}}
.claims li{{padding:10px 0;border-bottom:1px solid var(--rule);display:grid;gap:2px}}
.claims span{{color:var(--mute);font-size:14px}}
.item{{padding:12px 0;border-bottom:1px solid var(--rule)}}.item p{{margin:0}}
.cards{{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:12px}}
.card{{display:grid;gap:4px;align-content:start;padding:14px;min-height:44px;border:1px solid var(--rule);border-radius:8px;
background:var(--panel);color:inherit;text-decoration:none}}
.card:hover,.card:focus-visible{{border-color:var(--pr);outline:none}}
.card .t{{font-weight:600;font-size:18px}}
.card .f{{font-size:13px;color:var(--mute)}}.card .f b{{color:var(--ink);font-size:15px;font-variant-numeric:tabular-nums}}
.card .p{{font-size:14px}}
.card .go{{font-size:13px;color:var(--pr);margin-top:4px}}
.open{{padding-left:20px;margin:0}}.open li{{margin:0 0 8px;max-width:70ch}}
footer.band{{margin-top:36px;padding-bottom:40px;font-size:13px;color:var(--mute)}}
</style>
</head>
<body>
<header class="band">
  <h1>A Lean proof of the Riemann Hypothesis, and what has been checked of it</h1>
  <p>Levent Alpöge announced on 20 November 2026 a proof of the Riemann Hypothesis written in Lean 4, a language in which a
  program checks every step of a proof. This page leads to the work that reads the proof. It says what the proof claims, what
  has been checked and by whom, where each part can be read, and what is open.</p>
  <p><a href="../index.html">Open the proof explorer</a></p>
</header>
<main class="band">
  <h2>What the proof claims</h2>
  <p>The file <code>Main.lean</code> proves five theorems. The first is the Riemann Hypothesis, and the other four state it for
  the L-functions of Dirichlet characters.</p>
  <ul class="claims">{claims}</ul>
  <div class="stats">{''.join(f'<div class="stat"><b>{a}</b><span>{esc(b)}</span></div>' for a, b in stats)}</div>

  <h2>What has been checked, and by whom</h2>
  {checked_html}

  <h2>Where to read</h2>
  <div class="cards">{''.join(cards)}</div>

  <h2>What is open</h2>
  <ul class="open">{open_html}</ul>
</main>
<footer class="band">
  <p>The figures come from the files of the verification folders as they stood on {datetime.date.today().isoformat()}, when
  the page was built. A language model, Claude, wrote the readings and this page.</p>
</footer>
</body>
</html>
"""
    out = os.path.join(HERE, "overview", "index.html")
    with open(out, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"{len(cards)} cards, {len(checked)} checks, {len(derived) + len(noted)} open items, {os.path.getsize(out) / 1e3:.1f} kB")


if __name__ == "__main__":
    main()
