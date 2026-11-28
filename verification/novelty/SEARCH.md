# What a search of the literature by one language model found for each unit of the proof

The Lean source in [`src`](../../src) is a formalisation in Lean 4 that claims the Riemann
hypothesis and its form for Dirichlet L-functions. Its author announced it on 20 November
2026. This document asks which part of its mathematics was published before that day, and it
leaves the correctness of the proof aside. A language model searched the published literature
for 64 pieces of the proof, which are called units here, and gave each unit a class. It named
a published source for the result of 7 units and for the technique of 41 units, called 12
units bookkeeping of the proof, found 2 units too vague to compare and named no precedent for
2 units. The 2 units without a named precedent are the conclusion itself and a bound on how
divisible the values of a period are after a chain of theta lifts.

The model was gpt-6.2-sol of OpenAI, run through the Codex command line with web search on
27 and 28 November 2026. The brief was [`brief-gemini.md`](brief-gemini.md), which was written
for a run of Gemini. That run has not happened, because the quota of the Gemini account was
used up on 26 November and, by the message of the account, renews on about 30 November. It
stays planned as a second classification by a model of another maker, from the same brief and
the same repository.

## Words used here

- The Lean text is the source in `src`. The author is the person who wrote it and announced
  it. The note is a four-page [note](https://alpo.ge/remark.pdf) of the author. The commentary
  is [`README.md`](../strategy/README.md) of `../strategy`, which follows the route of the
  proof through the Lean text in nine steps. The project is all of these together.
- A unit is one of two things. 44 units are the rows of [`CLAIMS.md`](../strategy/CLAIMS.md),
  which list what the Lean text states at each of the nine steps and where the premises of the
  route come from. Unit 5.3 is the third row of step 5. 20 units are the entries of the
  timeline of the note, in which the author tells in dated entries from 6 October to
  20 November 2026 how the argument came about. Unit T10 is entry 10. The entries are
  paraphrased in [`units.json`](units.json). Some entries name an idea of an early stage, and
  some cover the same mathematics as a row, so the 64 units overlap. Unit T20 and unit 1.1
  both state the conclusion.
- A batch is one of the twelve groups in which `units.json` holds the units, one for each of
  the nine steps, one for the supply of the premises and two for the timeline.
- An answer is what the model wrote for one unit. It names the technique of the unit in the
  terms of the literature, gives a class, cites up to three sources with a place and a quote,
  and says in its field `difference` what differs between the unit and the nearest source.
- The five classes are those of the brief. K means that a source states the result. A means
  that the technique is published and that the unit uses it on another object, in another
  range or in a new combination. N means that the searches found no source for the result or
  for the technique. G means that the unit is bookkeeping without a technique of its own. U
  means that the unit is too vague or too much in the project's own words to compare.

## The counts

| Class | Rows of `CLAIMS.md` | Entries of the timeline | All |
|---|---:|---:|---:|
| K, a source states the result | 5 | 2 | 7 |
| A, a published technique in a new place | 27 | 14 | 41 |
| G, bookkeeping | 12 | 0 | 12 |
| U, too vague to compare | 0 | 2 | 2 |
| N, no precedent found | 0 | 2 | 2 |
| All | 44 | 20 | 64 |

The brief asked each answer to say how sure the model is of the class, as high, medium or
low. All 12 answers of class G and 6 of the 7 answers of class K are marked high. Of the 41
answers of class A, 12 are marked high and 29 medium. The two answers of class U are marked
low, and of the two answers of class N one is marked high and one medium.

## What the classes say and what they leave open

Class A holds 41 of the 64 units, and it is a wide class. An answer of class A says that the
technique is published, and its field `difference` says what the unit does with the technique
that the source does not do. Unit 5.3 shows the pattern. Its nearest source is Proposition 4.5
of Bost's paper of 2001, an inequality between the slopes of two lattices along one injective
map. The unit bounds the mean slope of one target lattice from many maps at once, and it
controls the maps together through bounds of the kind that the literature on frames calls
frame bounds. The answer cites the single-map inequality and a paper on frame potentials, and
says that the search found no source for the joined estimate. The brief told the model to
class a joining of two published results as A. The count of class N therefore leaves out every
unit whose new part is such a joining or a use on a new object, and a reader who asks what is
new in the proof has to read the differences of class A, which the section
[The differences](#the-differences) prints. Classes K and G, as the model applied them, claim
that nothing in the unit is new.

The two units of class N are these.

- T10 is the entry of the timeline on a lower bound for the divisibility of period values after
  a chain of theta lifts. The answer cites papers of Berger and of Brown and Klosin on the
  integrality and the congruences of a single lift, and says that it found none on the
  divisibility along a chain.
- T20 is the conclusion, the Riemann hypothesis for Dirichlet L-functions. The answer cites
  the statement as a conjecture and as a verified fact in bounded ranges, in Platt's
  computations.

The model did not apply the classes by one rule in two respects, and each batch ran in a
session of its own, which may be the reason.

- Unit 1.1 states the same conclusion as T20 and got class K, because its nearest source
  prints the statement as a form of the hypothesis. The brief does not say whether a result
  stated as a conjecture counts for class K. The 7 units of class K therefore include one
  whose result is published as a conjecture only, and the other six are published theorems
  or definitions by their answers.
- T10 got class N although its answer cites the technique for one lift, while unit 5.3 got
  class A with a source for one map. The answers do not say what separates the two cases.

The two units of class U are entries T4 and T6 of the timeline, which propose a determinant
proof of a positivity and a criterion with two cut-offs. The answers cite Weil's explicit
formula and a criterion of Freitas, and say that the entries leave the test function and the
quantifiers unstated.

[`ANCHORS.md`](ANCHORS.md) lists 13 published techniques that the note and the commentary
name, each with the units that name it, 18 units in all. An answer of class N for one of those
units would contradict an opened source. No such answer occurs. Units T4 and T6, which anchors
1 and 2 name, are of class U, and their answers cite sources of the kind the anchors name.
Every other unit that an anchor names is of class K or A. The model could read `ANCHORS.md` in
the repository, so the agreement shows that the two lists do not contradict each other, and it
is no blind test of the search.

## The quotes

The script [`quotes.py`](quotes.py) tried to download every cited address and looked for the
quote in the text that it got. The answers cite 109 quotes from 81 addresses.

| Outcome | Quotes |
|---|---:|
| Found. Every word of the quote stands in the downloaded text in order | 84 |
| Read. A formula, a line break or a scan broke the match, and the quote was found by reading | 17 |
| Unopened. The address gave no text of the source, so the quote is unchecked | 8 |

A quote counts as confirmed here when it is found or read. The language model Claude, which
wrote this document, did the reading at the place that the answer names, and
[`quotes.json`](../review/codex-novelty/quotes.json) says for each read quote what stands in
the source. One read quote differs from its source by one letter, in unit T6.

The 8 unopened quotes belong to units 1.2, 1.3, 3.8, 5.5, 7.2, 9.3, 10.2 and T19. One address
answered that the page does not exist, and the other seven answered with a page that holds no
text of the source, such as a check of the connection. An unopened quote may be right or
wrong.

53 units cite at least one source. They are the 48 units of classes K and A, the two of class
U, the two of class N, and unit 3.1 of class G, whose answer cites a textbook for a fact that
the bookkeeping uses. Of the 53 units, 45 have every quote confirmed, 7 have some quotes
confirmed, and unit 1.3, of class K with confidence high, has its one quote unopened.

A confirmed quote shows that the words stand in the source. It does not show that the source
supports the class of the answer. No source was read through to test a class.

One source is close to the proof in time. The answers to T1 and T4 cite a preprint of Banks,
On the OpenAI proof that Landau-Siegel zeros do not exist, arXiv 2610.15483, which arXiv dates
to 11 October 2026. It appeared before the announcement, so the brief admits it. Whether it is
independent of the proof here was not examined. The answer to T1 rests its class K on that
preprint and on Bombieri's exposé of Stepanov's method, so its class K holds without the
preprint only if the exposé alone carries it.

## The citations against three catalogues

A citation is the line in which an answer names a source, with the authors, the title, the
place of publication and the year. The answers hold 85 different citations. The script
[`metadata.py`](metadata.py) looked for records of each one in three catalogues.

- In arXiv, when the address or the citation holds an arXiv identifier.
- In Crossref, by a DOI that the address holds or that the arXiv record names, and otherwise
  by asking Crossref for the citation as free text.
- In zbMATH Open, by asking for the title.

An answer of a search counts as a record of the citation when its title stands in the citation
word for word and its first author stands there too. The script compared six fields of the
citation with each record. A field is the same when it agrees with at least one record. It
differs when it agrees with no record and differs from at least one.

| Catalogue | Citations with a record |
|---|---:|
| arXiv | 29 |
| Crossref | 62 |
| zbMATH | 68 |
| At least one of the three | 80 |
| All three | 15 |
| None | 5 |

| Field | Same as a record | Differs from every record that gives it | Citation does not give it | No record gives it |
|---|---:|---:|---:|---:|
| Authors | 80 | 0 | 0 | 0 |
| Title | 79 | 1 | 0 | 0 |
| Year | 79 | 1 | 0 | 0 |
| Journal or series | 72 | 2 | 4 | 2 |
| Volume | 27 | 0 | 35 | 18 |
| Pages | 8 | 0 | 71 | 1 |

In 77 of the 80 citations with a record no field differs. No citation has a wrong author, a
wrong volume or wrong pages by its records. Most citations give no pages, so the pages were
compared for 8 citations only.

The 3 citations with a field that differs are these, each read against its records by the
language model Claude.

- Bombieri, Le grand crible dans la théorie analytique des nombres, is cited in unit 3.6 as
  Astérisque 18 of 1974. The address that the answer opened is the file `AST_1987__18__1_0`,
  and the one record, of zbMATH, is the second, revised and enlarged edition of 1987. The
  citation therefore dates the first edition while the answer quotes the second, and a page
  or theorem number of one edition may not hold in the other.
- Bombieri, Counting points on curves over finite fields, is cited in unit 9.3 as Séminaire
  Bourbaki, exposé 430, Springer-Verlag, 1974. The Crossref record names the series Lecture
  Notes in Mathematics, which that citation leaves out and which the citation of the same
  exposé in unit T1 gives. The zbMATH record adds the words d'après S. A. Stepanov to the
  title, as the citation of unit T1 does.
- Weil, Sur les formules explicites de la théorie des nombres premiers, is cited with its
  first publication in Lund in 1952. zbMATH confirms the year 1952 and gives the place in an
  abbreviation that the script cannot compare, Meddel. Lunds Univ. Mat. Sem. The Crossref
  record is the reprint in the collected papers of 1979.

In 14 citations a field agrees with one record while another record has something else. These
are differences between the catalogues or between a preprint and its printed version, and the
file [`metadata.json`](../review/codex-novelty/metadata.json) names the records for each. Two
of the 14 are the citations of Bombieri's exposé and of Weil's article in the list above, and
the other 12 are these.

- The textbook of Montgomery and Vaughan is cited with 2006 in units 1.2 and 1.3 and with 2007
  in unit 3.1. Crossref has 2006 and zbMATH has 2007, so each citation has one catalogue
  behind it, and the two citations still disagree with each other.
- Four articles are cited with the year of their volume, which zbMATH also gives, while
  Crossref has the year in which the article went online. They are Ford, Green, Konyagin,
  Maynard and Tao (2018 against 2017), Chen and Zou (2025 against 2024), Furusawa and Morimoto
  (2021 against 2020), and, the other way round, Deligne's La conjecture de Weil I, which
  Crossref dates 1974 as the citation does and zbMATH 1973.
- Four citations give a preprint with its year on arXiv, and zbMATH or Crossref holds a
  printed version of a later year. They are Massey, Ruiz and Stojanoff (2008, printed 2010),
  Berger (2009, printed 2014), Brown and Klosin (2018, printed 2020), and Gan, Qiu and Takeda
  in unit T14 (2012, printed 2014). The answer to unit T9 cites the printed version of the
  last one.
- The titles of two preprints differ on arXiv from the printed titles that the citations
  give, for Bannai and Kobayashi and for Furusawa and Morimoto.
- Stepanov's article is cited in its English translation, which Crossref holds, and zbMATH
  holds the Russian original.

Five citations have no record in any of the three catalogues, so their fields are unchecked.
They are Riemann's paper of 1859, Chebyshev's memoir of 1852, Bost's exposé in Astérisque 237
of 1996, and the course notes of Milne and of Kedlaya.

## Every unit

The table gives the first sentence of the field `technique` of each answer, the first of its
sources by authors and the year that the answer gives, and how many of its quotes were
confirmed. The full answers, with the places, the quotes and the search phrases, are in
[`../review/codex-novelty`](../review/codex-novelty).

<!-- table starts -->

**Step 1, from the five theorems to one statement**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 1.1 | K | high | This is the right-half-plane formulation of the generalized Riemann hypothesis for Dirichlet L-functions. | Yifan Yang 2001 | 1 of 1 |
| 1.2 | K | high | The functional equation reflects a zero of a primitive Dirichlet L-function at s to a zero for the conjugate character at 1 − s. | Hirotaka Akatsuka and Ade Irma Suriajaya 2018 | 2 of 3 |
| 1.3 | K | high | This is the conductor reduction for Dirichlet L-functions. | Hugh L. Montgomery and Robert C. Vaughan 2006 | 0 of 1 |
| 1.4 | G | high | This declaration assembles premises for primitive Dirichlet zero-freeness. | none | none |

**Step 2, from a bound on intervals to zero-freeness**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 2.1 | A | high | The unit defines a positively weighted real combination of smoothed Chebyshev error terms for primitive Dirichlet characters. | Youness Lamzouri, Xiannan Li, and Kannan Soundararajan 2015 | 1 of 1 |
| 2.2 | A | high | This is a Landau-type oscillation criterion localized to intervals of the form [Y, Y^la]. | Jerzy Kaczorowski and János Pintz 1986 | 2 of 2 |
| 2.3 | A | medium | The unit obtains a one-sided smoothed prime-sum estimate by combining a Chebyshev-style comparison of divisibility and lattice size with finite character projection and bounds for the remaining characters. | Jean-Benoît Bost 1996 | 3 of 3 |

**Step 3, the wanted characters inside an auxiliary field**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 3.1 | G | high | The host condition uses the annihilator of the subgroup generated by the image of A0 and iod, then identifies its characters by their primitive Dirichlet representatives. | Hugh L. Montgomery and Robert C. Vaughan 2007 | 1 of 1 |
| 3.2 | G | high | `WinPair` specifies logarithmic size windows and congruences for two auxiliary primes. | none | none |
| 3.3 | G | high | The unit assigns a pointwise bound on the regularized, smoothed von Mangoldt sum to a sign-selected set of host characters. | none | none |
| 3.4 | A | medium | The unit applies zero-density exclusion and moment bounds in a two-stage selection of auxiliary primes, with simultaneous control of three quadratic twists. | Youness Lamzouri, The number of imaginary quadratic fields with prime discriminant and class number up to H 2017 | 3 of 3 |
| 3.5 | A | high | The unit combines a density estimate for zeros in a fixed-width rectangle with a maximal second-moment bound for short Dirichlet polynomials. | Youness Lamzouri, The number of imaginary quadratic fields with prime discriminant and class number up to H 2017 | 3 of 3 |
| 3.6 | A | high | The unit compares a large-sieve zero-density upper bound for excluded conductors with a lower bound from the prime number theorem for a reduced progression in the presence of a possible exceptional real zero. | Enrico Bombieri 1974 | 2 of 2 |
| 3.7 | A | high | The unit expands a second moment over prime-conductor quadratic characters and groups pairs by the squarefree kernel of their product. | Hugh L. Montgomery and Robert C. Vaughan 1979 | 2 of 2 |
| 3.8 | A | high | Quadratic reciprocity turns the pair correlation into a real Dirichlet character evaluated at the varying prime, up to a constant sign on the progression. | Youness Lamzouri, The number of imaginary quadratic fields with prime discriminant and class number up to H 2017 | 2 of 3 |

**Step 4, from the characters to an arithmetic quantity**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 4.1 | A | medium | The unit defines a Chebotarev prime-power sum with the linear weight (a/p^i − w)₊ and a separate term at the ramified prime d. | Yasutaka Ihara, On the Euler-Kronecker constants of global fields and primes with small norms 2006 | 2 of 2 |
| 4.2 | A | high | Finite character orthogonality rewrites the weighted Frobenius prime-power sum as a sum of smoothed character sums with inertia-averaged local coefficients. | Jeffrey C. Lagarias and Andrew M. Odlyzko 1977 | 2 of 2 |
| 4.3 | A | medium | Averaging translates over A0 projects the finite Fourier expansion onto the characters trivial on A0. | Terence Tao and Van H. Vu 2006 | 2 of 2 |
| 4.4 | A | medium | The unit uses bounds on the character averages over TT and on the variation of smoothed sums to transfer the projected estimate to the common argument x. | Yasutaka Ihara, V. Kumar Murty, and Mahoro Shimura 2009 | 2 of 2 |

**Step 5, two bounds on one slope**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 5.1 | G | high | The theorem transfers a conditional pointwise bound to a weighted prime-power sum indexed by the image of the record in H. | none | none |
| 5.2 | A | medium | DIV packages a pointwise upper bound for a dual Arakelov slope plus a logarithmic height bound for a composite map. | Frank Calegari, Vesselin Dimitrov, and Yunqing Tang 2024 | 2 of 2 |
| 5.3 | A | medium | This is a quantitative Arakelov mean-slope estimate for a family of lattice maps whose matrices are controlled by nearly tight frame bounds. | Jean-Benoît Bost 2001 | 2 of 2 |
| 5.4 | G | high | The proof takes a positive rank-weighted mean of pointwise inequalities and eliminates the common intermediate slope from the two bounds on that mean. | none | none |
| 5.5 | A | medium | Count5 controls an auxiliary level prime through a normalized logarithmic ratio involving unitary representation dimensions, Hermitian lattice masses and level indices. | Aidan Roy, Bounds for codes and designs in complex subspaces 2010 | 1 of 2 |

**Step 6, the lattices and the chain of lifts**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 6.1 | G | high | The predicate TieLocal identifies scalar inputs to the slope argument with invariants of the lattices assigned to each group element and word. | none | none |
| 6.2 | K | high | This is the Arakelov slope of a Euclidean lattice and its expression through restriction of scalars from a totally imaginary number field. | Jean-Benoît Bost and Klaus Künnemann 2010 | 2 of 2 |
| 6.3 | A | high | The unit applies the archimedean operator-norm part of the Arakelov height of a linear map to an integral map from each word lattice into a common dual lattice. | Jean-Benoît Bost 2001 | 2 of 2 |
| 6.4 | A | medium | The unit factors a word-indexed pairing through a chain of equivariant kernels on spaces carrying unitary-group actions, with coordinate and metric identifications at each stage. | Chenyan Wu 2013 | 2 of 2 |
| 6.5 | A | medium | The unit composes kernels in coordinates and forms the last matrix by contracting two kernels over intermediate classes with reciprocal stabilizer weights. | Chenyan Wu 2013 | 2 of 2 |

**Step 7, the bound for one lift**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 7.1 | A | medium | The estimate combines a Stirling-type lower bound for log factorials, a rowwise lower bound for the Young-diagram hook product, and telescoping bounds on gaps between interlacing weights. | Herbert Robbins 1955 | 3 of 3 |
| 7.2 | K | high | This is the elementary Young-diagram hook-product lower bound obtained by retaining the arm and the cell itself in each hook. | J. S. Frame, G. de B. Robinson, and R. M. Thrall 1954 | 1 of 2 |
| 7.3 | A | high | The numerical estimate uses strict Cauchy interlacing of two adjacent-rank rows, the pattern obtained by expressing compact unitary branching in Harish-Chandra coordinates. | Hongyu He 2017 | 1 of 1 |
| 7.4 | A | medium | The top-place contribution combines the leading logarithmic Stirling term with a weight times a quadratic CM period term in first Kronecker limit formula normalization. | Yasutaka Ihara, On the Euler-Kronecker Constants of Global Fields and Primes with Small Norms 2006 | 2 of 2 |

**Step 8, the lower bound**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 8.1 | G | high | This step instantiates a common-target slope inequality with the lattices and linear maps indexed by the words of the datum. | none | none |
| 8.2 | A | medium | This is a lower bound on the mean Arakelov slope of a common target, using a rank-weighted mean of source slopes shifted by morphism heights. | Jean-Benoît Bost 2001 | 2 of 2 |
| 8.3 | A | high | The proof expands the frame potential as a sum of squared Hilbert–Schmidt norms of Gram blocks and bounds the change under isometric compression. | Pedro G. Massey, Optimal reconstruction systems for erasures and for the q-potential 2009 | 2 of 2 |
| 8.4 | G | high | This step bounds total column count by multiplying a lower bound on the number of words by a uniform lower bound on the number of columns per word. | none | none |
| 8.5 | A | medium | This is a quantitative Gram-matrix estimate for normalized automorphic Bessel-period operators, combined with a matrix realization at one infinite place. | Philippe Michel, Dinakar Ramakrishnan, and Liyang Yang 2023 | 3 of 3 |

**Step 9, the exponent 1/2**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 9.1 | A | medium | The unit applies an Arakelov slope comparison and termwise error estimates to bound a smoothed prime-power discrepancy summed over a chain of theta lifts. | Frank Calegari, Vesselin Dimitrov, and Yunqing Tang 2025 | 2 of 2 |
| 9.2 | G | high | The unit defines a uniform error allowance B0 = f·m·b·x^ε with b = exp(x^ε), so the allowance itself grows linearly with the chain length m when the other parameters are held fixed. | none | none |
| 9.3 | A | high | The unit divides an aggregate inequality by its positive multiplicity and density factor, then estimates each normalized error term. | S. A. Stepanov 1969 | 1 of 2 |
| 9.4 | G | high | The unit substitutes GmA − SigA into the scalar size bound and rearranges the resulting inequality to bound the kept character sum. | none | none |

**The supply of the premises**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| 10.1 | G | high | This step instantiates a conditional family-existence theorem and passes its conclusion to the zero-free argument. | none | none |
| 10.2 | A | medium | The unit combines Green's parametrization of finite general linear group cuspidal characters with the attachment of ℓ-adic Galois representations to regular algebraic polarized cuspidal automorphic representations over CM fields. | Christophe Soulé 2003 | 2 of 3 |

**Entries 1 to 10 of the timeline of the note**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| T1 | K | medium | The entry names a Stepanov-style interpolation determinant, a method for turning vanishing or Frobenius congruences into a bound by comparing divisibility with size. | William D. Banks 2026 | 2 of 2 |
| T2 | A | medium | At a good inert prime the CM elliptic formal group has height two, and the vanishing Hasse invariant gives Dᵖ ≡ 0. | Nicholas M. Katz, Formal groups and p-adic interpolation 1977 | 3 of 3 |
| T3 | A | medium | The entry uses additive-character orthogonality on a path-shaped quadric to split a weighted count into a zero-frequency term and a remainder. | Pierre Deligne 1974 | 2 of 2 |
| T4 | U | low | The entry proposes to prove positivity of a Weil functional on an indicator using a determinant with first-order vanishing, then bootstrap the positivity. | André Weil 1952 | 2 of 2 |
| T5 | A | medium | The entry adopts a centered first Riesz mean of Λ(n)/n and uses the Guinand–Weil explicit-formula sign. | André Weil 1952 | 2 of 2 |
| T6 | U | low | The entry proposes a zero-free half-plane criterion from positivity on a test made from indicators at two scales, with relative weight of order X^η. | Pedro Freitas 2006 | 1 of 1 |
| T7 | A | medium | The entry proposes putting unitary Gan–Gross–Prasad periods into a determinant, using the multiplicity-zero-or-one branching law governed by interlacing of weights. | Hongyu He 2017 | 2 of 2 |
| T8 | A | medium | The entry iterates unitary theta lifts whose parameter rule adds one Hecke-character block per lift. | Rui Chen and Jialiang Zou 2021 | 2 of 2 |
| T9 | A | medium | The entry combines theta-lift norm and level calculations with CM period normalization, Weyl weight factors and Hermitian lattice masses. | Wee Teck Gan, Yannan Qiu and Shuichiro Takeda 2014 | 3 of 3 |
| T10 | N | medium | The entry concerns a lower valuation bound for period values after a chain of theta lifts. | Tobias Berger 2009 | 2 of 2 |

**Entries 11 to 20 of the timeline of the note**

| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |
|---|---|---|---|---|---|
| T11 | A | medium | The unit uses the finite layers of a cyclotomic ℤ₂-extension of a biquadratic CM field as auxiliary fields. | Lawrence C. Washington 1982 | 1 of 1 |
| T12 | A | medium | The unit uses seesaw unfolding to identify a period of an iterated definite-unitary theta lift with a Bessel period. | Wee Teck Gan and Atsushi Ichino 2016 | 2 of 2 |
| T13 | K | high | This is Bost’s Arakelov slope inequality for a linear map of Hermitian bundles. | Jean-Benoît Bost 2001 | 1 of 1 |
| T14 | A | medium | The unit combines the norm calculation for one theta lift with hook-product estimates for the archimedean weights. | Wee Teck Gan, Yannan Qiu, and Shuichiro Takeda 2012 | 2 of 2 |
| T15 | A | medium | The unit combines integral structures from several Hecke-character components to obtain a common divisibility constraint. | Haruzo Hida and Jacques Tilouine 1993 | 2 of 2 |
| T16 | A | medium | The unit uses a relative trace formula and Cauchy–Schwarz to reduce a period estimate to the squared norm of a projected Poincaré series. | Simon Marshall 2023 | 2 of 2 |
| T17 | A | medium | The unit bounds the sizes of the locally trivial classes in H¹(𝒪_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)) that remain after twisting. | Manfred Kolster and Abbas Movahhedi 2000 | 3 of 3 |
| T18 | A | medium | The unit assembles arithmetic covolume estimates, bounds on indices of lattices generated by theta series, and congruences between theta lifts and cusp forms. | Huayi Chen and Atsushi Moriwaki 2024 | 3 of 3 |
| T19 | A | high | The unit uses a Behrend digit-sphere construction to select many indices in the cyclic part of the auxiliary Galois group. | Felix A. Behrend 1946 | 1 of 2 |
| T20 | N | high | The claimed conclusion is Dirichlet GRH. | David J. Platt 2016 | 1 of 1 |

<!-- table ends -->

## The differences

The list gives the field `difference` of every answer of class A, N or U, in the words of the
model. Each entry says what the model found in the unit and not in its nearest sources. The
names in an entry, such as `PairGood`, are names of the Lean text.

<!-- differences start -->

- **2.1**, class A. Multiplying the source's sums by x gives the same weight, and Lemma 2.4 gives exactly the zeta main term x log x − (1 + γ)x. The Lean definition combines the centered terms with weight 1 on zeta and any distinguished character and weight 1/(3o + 1) on the remaining characters. The source uses an unweighted character sum for a subgroup calculation.
- **2.2**, class A. Taking T = Y^la and ε = 1 − 1/la gives exactly the interval used in the unit. The unit applies the one-sided test to a positively weighted family of smoothed errors and explicitly uses the positive residue at a real zero. The published sign-change proof uses repeated logarithmic integration, while Lean estimates high Taylor coefficients.
- **2.3**, class A. The Lean implication combines divisibility and slope bounds for lattices associated with iterated theta lifts with a character projection on an auxiliary field. Its hypotheses supply the character estimates and lattice data used to obtain x^(1/2 + (eD + eL + 7)ε), with eD and eL fixed across small ε. The top-level application uses intervals [Y, Y^(3/2)].
- **3.4**, class A. The unit selects q first and then d in a progression depending on q, with simultaneous bounds for all base characters modulo M and all three nontrivial twist choices. `PairGood` controls the regularized sums throughout [Y, Y^A], includes the bound 4 log y on the logarithmic derivative at 1, and imposes fixed-width zero-free boxes up to heights that grow with Y.
- **3.5**, class A. The unit applies these techniques inside a single admitted progression and simultaneously to a bounded number of primitive base characters with conductors at most F ≤ √U. Its condition also controls the logarithmic derivative at 1 and the regularized von Mangoldt sum over the entire interval [Y, Y^K], using a cutoff at Y^(400K).
- **3.6**, class A. The classical density estimate gives a stronger bound than Q^(1/4) at real part 399/400 and height Q. The unit projects that estimate to primes p > F through conductors f·p with f ≤ F, and combines it with the lower bound U^(9/10) for its admitted progressions.
- **3.7**, class A. The unit averages over one growing-modulus residue class and uses coefficients bounded by Λ(n) min(1, y/n) to obtain the factor y log y per candidate prime. It permits factors of the progression modulus and one exceptional squarefree kernel in the pair expansion, with each prime divisor of the progression modulus required to be at most Y^(ε/5) or above Y^(400K).
- **3.8**, class A. The unit gives an exact absolute-value identity by absorbing the factors of n·n′ supported on the progression modulus into a constant sign. It extends the cancellation argument from a fixed class modulo 4 to growing admitted moduli divisible by 8, with a relative bound Y^(−B′) for all but one coprime squarefree kernel r ≤ Y^A′.
- **4.1**, class A. With constant w and the stated splitting at 2 and q1, the prime sum follows from twice Ihara’s unnormalized sum over the rationals minus the corresponding sum over the quadratic subfield, at x = a/w, multiplied by w. The Lean definition lets the Frobenius power determine w through a translated class, so the cutoff a/w can vary with the class and the lift.
- **4.2**, class A. The Lean identity combines the inertia-aware class expansion with a separate rescaling y = a/w for each class and allows arbitrary centering data ℓ. Summation over the complement of an index-two subgroup retains the quadratic component of ℓ, and the translation to PhiSet gives the mean of log w in MAIN.
- **4.3**, class A. Tao and Vu give the projection identity for any finite abelian group, and Ihara treats cutoff variation for a scalar prime sum. The Lean inequality combines the projection with two weight ranges and a per-lift cost of 2b/x, yielding the normalization m·b·|T2|/(2|H|) before averaging over TT.
- **4.4**, class A. The earlier analytic estimate controls the discarded characters to obtain moments, while ch_core takes a one-sided bound for the aggregate prime sum and carries the discarded characters as the explicit remainder SigA. The exponent 1/2 + (C + 3)ε comes from the assumed error bracket and the size windows, including the window for m and the lower bound on |T2|/|H|.
- **5.2**, class A. Calegari, Dimitrov, and Tang bound a degree using heights of evaluation maps on power series. DIV bounds a common dual slope plus a word-dependent height and subtracts the offset Fo. Its main term sums m copies of the CM-normalized expression a log a − a − a logOm at each designated place and deducts a log T once at that place.
- **5.3**, class A. Bost’s inequality uses one injective map and the maximal target slope. The frame estimate supplies rank control for the combined images of the maps in the Harder–Narasimhan filtration, leading to a bound for the mean target slope with a log-cardinality loss and a correction depending on the slope excess, frame defects and HH. The accompanying HHBound imposes the additional scale cap x^cHH b.
- **5.5**, class A. The unit uses Weyl dimension factors and Hermitian lattice masses in a ratio that fixes the scale of a word-dependent auxiliary prime. It requires a lower bound built from the place averages of log(wv/π) and the two fixed level primes, an upper bound of order mL and variation of order log k across words. The π/v cancellation in key_identity5 follows algebraically after that lower bound is substituted.
- **6.3**, class A. For a totally imaginary field, htMap is twice the archimedean part of the usual normalized height because it uses squared operator norms. The finite-place terms of the usual height are nonpositive for a lattice-preserving map, and WordFacts takes a separate upper bound h as a hypothesis for each nonzero word map.
- **6.4**, class A. Wu composes a lift and a return lift, while Chen and Zou use one stable-range step with a quasi-split unitary target in the unitary case. The Lean theorem conditionally realizes a prescribed word pairing via a chain of arbitrary length m, with rank k + j(t + 1), a terminal rank-one extension, and exact coordinate and metric ties.
- **6.5**, class A. Lean combines the two-kernel composition with reciprocal stabilizer weights and an additional sum over a finite set attached to each intermediate class. For m ≥ 2, this coupling occupies the last of m − 1 matrices, and a supplied map into a dual space follows the matrix product.
- **7.1**, class A. The unit combines these inputs for two specific arrays of rows whose shifts depend on the lift index. The row pairing changes at top places so that a log a − a survives there, and the theorem gives a simultaneous weight-sum estimate with explicit allowances for the extra blocks and the top-place correction.
- **7.3**, class A. The inequality pattern agrees term for term. Lean assumes it for the code-dependent rational row uW, whose interior entries include a half-unit shift and an optional further offset, and for the first k − 1 entries of sigPar. He uses the inequalities to characterize compact unitary restriction, while Lean uses them to compare the shifted rows in a factorial estimate.
- **7.4**, class A. Writing K for the imaginary quadratic field and γ_K for its Euler–Kronecker constant gives logOm = 2γ + log(π/v) − γ_K by quadratic zeta factorization. The unit uses half the root discriminant of the host field for v and combines this normalized constant with the Stirling term as a log a − a − a logOm for each lift at each top place.
- **8.2**, class A. Bost compares slopes along a single injective map, and Bodmann controls overlaps of random orthogonal projections. The unit uses deterministic weighted Gram bounds with variable block sizes, additional rows, and a controlled loss of columns to lower-bound the mean slope of one target over a totally complex number field. Its correction depends explicitly on the excess of maximal source slope over the shifted mean, the target minimum slope, and the frame errors.
- **8.3**, class A. The unit turns blockwise estimates into a near-minimal frame potential and an aggregate diagonal Gram bound after compression. It applies the one-map slope inequality to the image of each source filtration step, uses the frame estimates to bound the codimension of their sum, and integrates this bound to control the target mean slope. The sharper Lean theorem proves the estimate before the nonnegative logarithm of the number of maps is subtracted.
- **8.5**, class A. The unit requires simultaneous Hilbert–Schmidt bounds for individual operator blocks in a deterministic word family, with off-diagonal scale duS(u)·duS(u′)/Dstar and diagonal blocks close to the identity. It gives exp(−x^(ε/8)) control on the off-diagonal relative error, the square root of the diagonal error parameter, and the relative row-count error. It also identifies the target row block with a lattice morphism using BesselId, adding an arithmetic realization to the period estimates.
- **9.1**, class A. Calegari, Dimitrov, and Tang estimate the heights of graded evaluations of power series for Diophantine approximation. Here the slope comparison controls a weighted prime-power sum over theta lifts, with the bracket nT·aE·(1 + m²/k) + m·(B + N) and explicit hypotheses on the two budgets. The summand nT·aE is charged once in this estimate, which is what lets the next step divide that term by m.
- **9.3**, class A. The finite-field arguments divide a degree bound by a vanishing multiplicity, while the Lean lemma divides a prime-sum inequality by nT·m·b·((nT2/n)/2), with m counting theta lifts in its application. The Lean lemma assumes the window for m and uses the rank bounds, the density lower bound, and 26 ≤ x^(3ε/8) to obtain the explicit exponent 1/2 + (C + 3)ε.
- **10.2**, class A. Green works over all finite fields, while the Lean parametrization uses prime fields, and the Lean Galois-representation statement uses a weaker comparison away from ℓ than the published Weil–Deligne isomorphism. VWin requires finiteness and a single bound of exp(x^ε/2) for the sum weighted by log ℓ over arbitrary finite prime sets and all positive integers e below floor(x^401), using the localization kernels for ℚℓ/ℤℓ(−e) over specified cyclotomic subfields throughout windows [Y, Y²]. The cited results provide precedents for the inputs and for cohomology bounds, while this unit combines them with the window estimate and a compatible unitary kernel chain for every word.
- **T2**, class A. Katz’s slope expands as 1/p + 1/p³ + 1/p⁵ + ⋯ under his formal-function hypotheses. The timeline applies that slope with a logarithmic loss to a particular theta section normalized by Ωᵃ, so the trivialization, integrality and torsion-trace hypotheses determine how closely the results match.
- **T3**, class A. Deligne obtains positivity from even powers of traces and uses the poles of an Euler product. The timeline instead pairs a signed path-quadric count with iterated Parseval, and presents the sixfold GL₅ realization of N as a proposed construction. Friedberg and Ginzburg give global integrals for different covering groups and inputs.
- **T4**, class U. Weil tests convolution squares, and Banks bounds the valuations of an algebraic determinant. The timeline proposes a determinant proof of W(1_S) ≥ 0 but leaves the test set, determinant identity and bootstrap step unspecified.
- **T5**, class A. The timeline and Lean’s Gz use the weight (X/n − 1)₊. For this weight the shifted Perron integrand is −(ζ′/ζ)(1+s)X^(1+s)/(s(s+1)), and its double pole at s = 0 gives X log X − (1 + γ)X. The variance test is the additional proposed application, and the note leaves its test and averaging measure unspecified.
- **T6**, class U. Freitas tests an entire sequence of generalized Li coefficients for ζ. The timeline instead specifies two cutoffs in one X-dependent test and a boundary at 1 − η, while leaving the normalization of W, the quantifier on X and the family of L-functions implicit.
- **T7**, class A. The binary value in He’s branching rule is the dimension of a local multiplicity space. Kieburg encodes interlacing of eigenvalues by a determinant. The timeline proposes a determinant for W using period entries and refers to up to m failures of interlacing without identifying the quantity being counted.
- **T8**, class A. The sources describe one lift at a time and make the parameter twists and nonvanishing conditions explicit. The timeline uses successive totally definite groups with an unbounded number of lifts, treating their contributions as arithmetic multiplicity and balancing the X/m and m errors at m ≍ √X.
- **T9**, class A. The sources evaluate separate norm, period and mass quantities. In the project, divisor_inequality_assembly uses an identity for the sum of the weights to cancel terms involving the shift times the CM period logarithm at each lift, with a residual error, and then sums the bounds over the chain.
- **T10**, class N. Berger treats integrality of a single lift, and Brown and Klosin study coefficients of a single Ikeda lift for use in congruences. The timeline’s quantitative object is the ideal of values of a period pairing after m lifts, with contributions at selected primes and losses from passing to the integral lattices used in the comparison.
- **T11**, class A. The finite-field analogy and the cyclotomic tower are classical. The unit uses the cyclic factor to organize Frobenius orbits over the compositum with two imaginary quadratic fields, with the quadratic primes chosen for the Dirichlet-character argument.
- **T12**, class A. The precedents give a local unitary seesaw and a global period transfer for a single lift on a different dual pair. The unit iterates the transfer along a global definite-unitary chain and asserts independence from its varying Hecke characters. The Lean interface `BesselId` allows a nonzero scalar and isometries indexed by the input word, so the normalization matters for the independence claim.
- **T14**, class A. The project compares log-factorials with log hook products at each lift and uses the resulting inequality in its slope and prime-sum estimates. After main-term cancellation, the final division leaves leading scales x/m and m. The announced earlier 2/3 barrier has no matching derivation in the sources examined or in the final size estimate.
- **T15**, class A. The precedents measure congruences in p-adic Hecke families. The unit describes common integral data for the word-indexed maps of a definite-unitary lift chain, with a shared target lattice whose slope enters an average. The correspondence between that target lattice and the timeline’s greatest common divisor is tentative.
- **T16**, class A. Marshall bounds a unitary period for a depth-aspect subconvexity problem. The unit routes the norm estimate into a simultaneous bound on the Hilbert–Schmidt overlaps of integral columns and uses that bound in a lattice slope estimate. The note also mentions an earlier sixfold-cover argument whose relation to the final projection remains unclear.
- **T17**, class A. The degree-one localization kernel in the unit is the Poitou–Tate dual object to a higher étale wild kernel, with the usual local conventions. The project needs a simultaneous bound over primes and twists on varying CM host fields at the size required by the lift argument. Kummer–Vandiver supplies a vanishing comparison for specific class-group eigenspaces.
- **T18**, class A. The sources treat asymptotic arithmetic volumes, theta maps for specified lattice genera, and congruences for p-adic Yoshida families. The project combines finite-scale covolume bounds with a scaled theta-lattice index and congruence bounds for its definite-unitary chain over varying host fields.
- **T19**, class A. Behrend avoids three-term progressions, while `HostThickExists` enlarges the digit base to avoid all relations of the specified bounded-coefficient form and obtains a lower bound depending on that coefficient limit. The orbit lemma applies the selected indices inside a cyclic Galois layer, giving a concrete interpretation of the note’s link between Behrend and the tower choice.
- **T20**, class N. Platt proves a bounded verification in modulus and height. The unit asserts the unrestricted zero statement for all moduli and heights, and the Lean entry points include the passage from primitive characters to arbitrary Dirichlet characters.

<!-- differences end -->

## Limits

- One model made the classification in one run for each batch, and no second model has
  classed the same units. The planned run of Gemini would give that comparison.
- No mathematician has read the answers. The brief asks each answer for the point that a
  specialist should check first, and those points are in the field `specialist`.
- The comparison of the citations with the catalogues covers the description of a work. A
  citation that agrees with its record can still be attached to a claim that the work does
  not make.
- Class N says that a search found no source for the result or the technique. A source may
  exist that the search did not reach.
- Class A does not separate a routine use of a technique from a use that needed a new idea.
  That judgement needs a specialist of the field of each unit.
- Class G is the model's judgement that a row carries no technique, and no search stands
  behind it. Nobody checked the 12 rows of class G against the Lean text for this document.
- The model had the whole repository to read. For a row it was given the row, the commentary
  and the Lean text, and for an entry of the timeline the paraphrase and the address of the
  note. Which of these files it opened for a unit was not recorded.
- The brief asks for a synthesis after the twelve batches. Each batch ran in a session of its
  own, so the prompt left the synthesis out, and none was made.

## Running it

```
python3 -I verification/novelty/quotes.py
python3 -I verification/novelty/metadata.py
python3 -I verification/novelty/search.py
```

The first command downloads the sources into `verification/novelty/data/sources`, which git
ignores, and writes `quotes.json`. It needs `curl` and `pdftotext`. The second command asks arXiv,
Crossref and zbMATH for the records, with pauses between the calls, keeps their answers in
`verification/novelty/data/catalogue` and writes `metadata.json`. The third command writes
the table of the section Every unit and the list of the section The differences, and prints
the counts that the hand-written prose quotes. The answers themselves came from twelve runs of
this form, one for each batch.

```
codex --search exec -m gpt-6.2-sol -c model_reasoning_effort=high -s read-only -C <repository> -o <batch>.json "<prompt>"
```

The prompt told the model to read `brief-gemini.md`, to follow it for the one named batch, to
give the JSON array as its whole answer and to leave out the synthesis.
