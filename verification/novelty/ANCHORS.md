# Published techniques that the proof names, each with a source

The Lean source in [`src`](../../src) holds a proof that claims the Riemann hypothesis. A
four-page note of its author and the commentary on the strategy of the proof name published
results that the proof uses. This document lists 13 of them, each with a web page that was
opened on 25 November 2026 and with what that page states. Most of the 13 are methods or
theorems, anchor 9 is a formula, and anchors 8 and 13 are conjectures. The document calls them
all techniques. The list shows that each technique has a published source. It does not show
that the proof uses a technique in the way the source does, and it says nothing about the
steps of the proof that name no technique.

The list is a first set of fixed points for the search of the literature that
[`README.md`](README.md) describes. An answer of that search that classes one of these
techniques as without precedent can be checked against the page given here for that technique.

A language model, Claude, chose the techniques and the pages. A separate run opened each page
and reported its title and the sentences quoted below. A page of an encyclopedia serves here to
find the original papers, which it cites, and the original papers themselves were not opened
unless the entry says so. No mathematician has checked the list.

## Words used here

- The note is the four-page [note](https://alpo.ge/remark.pdf) of the author of the proof. Its
  timeline has 20 entries, which [`units.py`](units.py) paraphrases as T1 to T20.
- The strategy is the commentary [`README.md`](../strategy/README.md) of `../strategy`, which
  follows the route of the proof through the Lean text. A row is a row of
  [`CLAIMS.md`](../strategy/CLAIMS.md), which lists what the Lean text states at each step of
  that route. Row 5.3 is the third row of step 5.
- A technique is anchored when a page that was opened states it or names the paper behind it.

## The anchors

| No. | Technique | Where the proof names it | Page that was opened | Paper behind the anchor, or papers that the page cites |
|---:|---|---|---|---|
| 1 | Stepanov's elementary method for the Riemann hypothesis for curves over finite fields | T1, T4 | Wikipedia, Sergei Stepanov (mathematician) | Stepanov 1969, Bombieri 1972/73 |
| 2 | Weil's criterion, the positivity that is equivalent to the generalized Riemann hypothesis | T5, T6 | Wikipedia, Weil's criterion | Weil 1952 and 1972 |
| 3 | Landau's theorem on Dirichlet series with non-negative coefficients | row 2.2 | arXiv 1009.0228, abstract | Landau's theorem, named in the abstract |
| 4 | Slopes of hermitian vector bundles over number fields, after Bost | T13, rows 5.3 and 6.2 | arXiv math/0605408, abstract, and the Numdam record of Bost's exposé | Bost 1996 |
| 5 | The theta correspondence for a reductive dual pair | T8, row 6.4 | Wikipedia, Theta correspondence | Howe 1979, Weil 1964 |
| 6 | The formula of Siegel and Weil for the theta series of the lattices of a genus | T9 | Wikipedia, Siegel-Weil formula | Siegel 1951 and 1952, Weil 1964 and 1965 |
| 7 | The Rallis inner product formula for global theta lifts | T12 | arXiv 1207.4709, abstract | Gan, Qiu and Takeda 2012 |
| 8 | Restriction problems for classical groups and central critical L-values, after Gan, Gross and Prasad | T7 | arXiv 0909.2999, abstract | Gan, Gross and Prasad 2009 |
| 9 | The Chowla-Selberg formula | T9 | Wikipedia, Chowla-Selberg formula | Lerch 1897, Chowla and Selberg 1949 and 1967 |
| 10 | The hook length formula for Young diagrams | rows 7.1 to 7.3 | Wikipedia, Hook length formula | Frame, Robinson and Thrall, 1953 by the page |
| 11 | Green's computation of the characters of the general linear groups over finite fields | row 10.2 | arXiv 0706.0058, introduction | Green 1955 |
| 12 | Galois representations attached to regular algebraic cuspidal automorphic representations, without a hypothesis of self-duality | row 10.2 | arXiv 1411.6717, abstract | Harris, Lan, Taylor and Thorne 2014 |
| 13 | The Vandiver conjecture and the K-groups of the integers | T17 and its footnote | Wikipedia, Kummer-Vandiver conjecture, and the Numdam record of Kurihara's paper | Kurihara 1992 |

## What each page states

1. The [page on Stepanov](https://en.wikipedia.org/wiki/Sergei_Stepanov_(mathematician))
   dates his proof to 1969 and calls it a proof "using elementary methods of the Riemann
   hypothesis for zeta-functions of hyperelliptic curves over finite fields". It says that
   Schmidt extended the method to the general case and that Bombieri gave "a substantially
   simplified, elementary proof". It cites Stepanov, On the number of points of a hyperelliptic
   curve over a finite prime field, 1969, and Bombieri, Counting points on curves over finite
   fields, Séminaire Bourbaki 1972/73.
2. The [page on Weil's criterion](https://en.wikipedia.org/wiki/Weil%27s_criterion) says that
   the criterion "takes the form of an equivalent statement, to the effect that a certain
   generalized function is positive definite". The page states it for the generalized Riemann
   hypothesis and cites two papers of Weil, Sur les formules explicites de la théorie des
   nombres premiers, 1952, and a paper of nearly the same title of 1972. The note names Guinand
   beside Weil, and the page was not searched for Guinand.
3. The abstract of [arXiv 1009.0228](https://arxiv.org/abs/1009.0228), by Maurizi, states
   Landau's theorem in these words, "if an ordinary Dirichlet series has non-negative
   coefficients, then it has a singularity on the real line". The commentary of the strategy
   calls the mechanism of row 2.2 a Landau argument.
4. The abstract of [arXiv math/0605408](https://arxiv.org/abs/math/0605408), by Gaudron, says
   that "J.-B. Bost developped a slope theory of hermitian vector bundles over number fields".
   The [Numdam record](https://www.numdam.org/item/SB_1994-1995__37__115_0/) gives Bost's
   exposé as Périodes et isogénies des variétés abéliennes sur les corps de nombres, Séminaire
   Bourbaki, exposé 795, Astérisque 237, 1996. The record has no abstract, so the slope
   inequality itself was not read.
5. The [page on the theta correspondence](https://en.wikipedia.org/wiki/Theta_correspondence)
   defines it as "a mathematical relation between representations of two groups of a reductive
   dual pair". It credits Howe, θ-series and invariant theory, 1979, and takes the name from
   Weil 1964. The note speaks of a chain of such lifts between unitary groups, and the page was
   not searched for chains.
6. The [page on the Siegel-Weil formula](https://en.wikipedia.org/wiki/Siegel%E2%80%93Weil_formula)
   says that the formula "expresses an Eisenstein series as a weighted average of theta series
   of lattices in a genus". It cites Siegel, Indefinite quadratische Formen und
   Funktionentheorie, 1951 and 1952, and Weil, Sur certains groupes d'opérateurs unitaires,
   1964, and Sur la formule de Siegel dans la théorie des groupes classiques, 1965. Entry T9 of
   the note names the Siegel mass. The page states the formula of Siegel and Weil, whose
   weights are the inverses of the orders of the automorphism groups, and it was not searched
   for the mass formula itself.
7. The abstract of [arXiv 1207.4709](https://arxiv.org/abs/1207.4709), by Gan, Qiu and Takeda,
   says that the authors "derive the Rallis inner product formula for global theta lifts for
   any dual pair". Entry T12 of the note names Rallis with a seesaw, and the abstract was not
   read for the word seesaw.
8. The abstract of [arXiv 0909.2999](https://arxiv.org/abs/0909.2999), by Gan, Gross and
   Prasad, says "We formulate several conjectures about these restriction problems", which
   concern classical groups and a "central critical L-value in the global case". The abstract
   states conjectures, so this anchor shows that the periods which entry T7 names belong to a
   published set of conjectures.
9. The [page on the Chowla-Selberg formula](https://en.wikipedia.org/wiki/Chowla%E2%80%93Selberg_formula)
   says that the formula "is the evaluation of a certain product of values of the gamma
   function at rational values". It says that Lerch essentially found it in 1897 and cites
   Chowla and Selberg, On Epstein's zeta-function, 1949 and 1967.
10. The [page on the hook length formula](https://en.wikipedia.org/wiki/Hook_length_formula)
    gives the number of standard Young tableaux of a shape as n! divided by the product of the
    hook lengths, and says that the formula "was discovered in 1953 by Frame, Robinson, and
    Thrall". Row 7.2 of `CLAIMS.md` states an inequality between the factorials of the lengths of
    the rows of a Young diagram and its hook product. The page does not state that inequality.
    It gives an exact formula with the same product.
11. The introduction of [arXiv 0706.0058](https://ar5iv.labs.arxiv.org/html/0706.0058), by
    Aubert, Onn, Prasad and Stasinski, says that the irreducible characters of the general
    linear groups over a finite field "were computed by J. A. Green in 1955" and that the
    cuspidal representations "were shown to be in canonical bijective correspondence with
    Galois orbits of norm-primitive characters". The statement about cuspidal representations
    names no author.
12. The abstract of [arXiv 1411.6717](https://arxiv.org/abs/1411.6717), by Harris, Lan, Taylor
    and Thorne, speaks of "the compatible system of l-adic representations associated to a
    regular algebraic cuspidal automorphic representation" and says "The main innovation is
    that we impose no self-duality hypothesis on the automorphic representation". The Lean
    proposition that the code names `Row` treats polarized representations, which is a case
    with such a hypothesis, so the innovation of the paper is not what `Row` needs. Earlier
    papers treat the polarized case, and no page was opened for them.
13. The [page on the Kummer-Vandiver conjecture](https://en.wikipedia.org/wiki/Kummer%E2%80%93Vandiver_conjecture)
    says "Kurihara showed that the conjecture is equivalent to a statement in the algebraic
    K-theory of the integers", namely that the K-groups of ℤ of an index divisible by 4 vanish.
    It cites Kurihara, Some remarks on conjectures about cyclotomic fields and K-groups of Z,
    Compositio Mathematica 81, 1992, and the
    [Numdam record](https://www.numdam.org/item/CM_1992__81_2_223_0/) confirms that reference.
    A footnote of the note says that its author believes that the vanishing of several K-groups
    of ℤ follows from the proof. The anchor shows that the link between the conjecture and
    those K-groups is published. The conjecture itself is open.

## What has no anchor here

Ten entries of the timeline have no anchor in this list. Entries T2, T3, T10, T14, T15 and T18
describe computations and steps of the argument itself, and entry T20 is the conclusion.
Entries T11 and T19 name an Iwasawa tower and a result of Behrend, and entry T16 names a
relative trace formula with Poincaré series. No page was opened for those three. Two pages
that were tried did not load, a page of the American Institute of Mathematics on Weil's
criterion and the page of the Journal of the American Mathematical Society for the paper Theta
dichotomy for unitary groups.

## Limits

- An anchor shows that a technique is published. Whether the proof needs the published form,
  a special case or a new form is the question of the search of the literature.
- Seven of the 13 anchors rest on a page of Wikipedia. Five rest on the abstract of a preprint,
  anchors 3, 4, 7, 8 and 12, and anchor 11 rests on an introduction. The preprints of anchors
  7, 8 and 12 treat the technique themselves, and the other pages report it. The abstract of
  anchor 3 names Landau's theorem without citing a paper of Landau.
- The sentences in quotation marks were reported by the run that opened the pages, and this
  document repeats them as reported.
