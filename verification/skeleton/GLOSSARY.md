# Glossary of the ten definitions that the readings leave unopened most often

[`READING.md`](READING.md) says for each of the 38 lines of the outline what its Lean statement
claims, and it lists the ten names that stay unopened in the largest numbers of lines. This
document opens those ten. The readings were written by a language model and checked by further
runs of the same model. No mathematician has checked them.

The ten definitions are two records of data, one function that builds a record, two
propositions without arguments and five predicates. Each of them has further definitions of
the project below it, in the sense defined after the table, and the counts run from 13 to
4,236. The readings of the ten leave names unopened 487 times, where a name counts once for
each reading that leaves it unopened. Opening one layer of this vocabulary therefore does not
close it.

## The ten definitions

| Definition | What it is | Parts read | Definitions below it | Shown to the readers | Confidence |
|---|---|---:|---:|---:|---|
| `RecTExists` | a proposition without arguments | 6 | 357 or more | 99 | medium |
| `D7` | a record type with 141 fields | 141 | 282 | 42 | medium |
| `UnitaryGroupThirdPlaceHypotheses` | a bundle of 60 propositions, without arguments | 60 | 2,189 or more | 92 | medium |
| `LinkedAt` | a predicate of a parameter record and a relation | 10 | 4,236 or more | 84 | medium |
| `parametersOfDependence` | a function that builds a record | 7 | 3,453 or more | 87 | medium |
| `SlotNormCondition` | a predicate with three arguments | 7 | 3,404 or more | 87 | medium |
| `BoundAtTwoThreeFamilyFonAlt` | a predicate of a family record | 13 | 1,235 or more | 63 | medium |
| `KPx` | a predicate of two records | 5 | 71 | 71 | medium |
| `BundleCondition` | a record type with seven fields and three arguments | 10 | 3,045 or more | 57 | medium |
| `MIstar2` | a predicate of a record, a function and two maps | 8 | 13 | 13 | low |

A proposition is a statement that is true or false, and a predicate is a proposition that
depends on arguments. A part is a field of a structure, a conjunct of a proposition or an
argument of a function, and the column Parts read counts the parts that the first reading
lists, which can include the type of a result or a bound variable.

A definition lies below another when a chain of definitions leads to it, where each
definition of the chain is named in the text of the one before. The count follows such chains
for twelve levels, and a count carries the words or more when some chain goes on past the
twelfth level. Every count is a lower limit for a second reason as well. It leaves out a
definition that is written after a dot, as `X.MIUnit2` is, because the declaration graph does
not resolve such a name. The fifth column counts the definitions whose text the dossier of the
entry showed to the readers.

## What the readings say

Every name in code font is a name of the source. The sentences marked as suggestions come from
names and are not shown by the Lean text.

- `RecTExists` is a proposition. It says that for every number field E, every algebraic closure
  Ω of E, every valuation subring A of Ω, every height one prime w of the integers of E and
  every proof h that A lies over w, a map rc exists that meets the condition `IsRecT h rc`. The
  map goes from a type `IrrGL` over the completion of E at w to a type `WD h`. `IsRecT` asks
  for a homomorphism a from an object `Weil h` to the units of that completion that meets
  `IsLocalArtin`, and for twelve laws bundled in `LawsT`. As a suggestion, the names point to
  the existence half of a local Langlands correspondence.
- `D7` is a record type with 141 fields. An object of it is one bundle of data with proofs of
  conditions that tie the data together. Among its fields are a rank record `R`, a host
  record, a family of Hermitian spaces `sp`, a rows record `what₂`, a family of members
  `mem u`, lattice data, a commutative group with characters `muTil` and `chiD`, and local
  theories at every prime.
- `UnitaryGroupThirdPlaceHypotheses` is a bundle of 60 propositions without arguments.
  Fifty-six fields are single named statements, most of them in a namespace `Published`. Three
  fields are smaller bundles. The sixtieth field, `siegelEisensteinSimplePole`, has a type that
  unfolds to `True`, so it asserts nothing.
- `LinkedAt` takes a parameter record p and a relation r on pairs of a slot and a linkage. It
  says that a slot R exists such that a condition `LargeBaseCondition` holds for `KPx`, the
  slot `IsBuiltE p.s` and R, and such that r holds of the slot `IsGoodE p.s` joined with R,
  paired with the linkage `BundleLinkage p`. A slot is a predicate on tuples of a context, a
  record of stages, a frame, twisting data and a core record.
- `parametersOfDependence` is a function. From a proof hL of `RecTExists` and a real number
  cDep it builds a record with the four fields R, N, S and Γ, which it fills with `RX`,
  `extensionWithList hL cDep`, `SExt.none` and `geoCl anyGeometry`.
- `SlotNormCondition` takes a slot Q, a link predicate Lk and a property N of family classes.
  It is the proposition `Row Q Lk H`, where H sends a family class 𝒜 and a selection to the
  statement that N holds of the class `D3 3 𝒜`. Unfolded one step, it says that a map E exists
  with `RowE Q Lk E` such that for every family class 𝒜 and every raw selection σ with
  `IsSel Q Lk E 𝒜 σ` the property N holds of `D3 3 𝒜`. This `Row` takes three arguments and is
  another definition than the `Row` of line 2 in `READING.md`.
- `BoundAtTwoThreeFamilyFonAlt` takes a family record Fm. It says that real numbers C and x0
  exist such that for every x ≥ x0 and all further data of the family at x, the condition
  `SetupAlt` implies the condition `BoundAtTwoThree` with the constant C. The same C serves
  the whole family.
- `KPx` takes a record B and a record f. It is the conjunction of two statements. The first
  says that a record δ exists that meets a condition `B.KsExact δ f`, and the second is a
  condition `PrePin` on B.
- `BundleCondition` is a record type with seven fields over three arguments, a datum D of the
  type `D7`, an object O and a real number c. Five fields are data, one is a proof, and one is
  a pair of natural numbers with two equations.
- `MIstar2` takes a record X, a function fc and two maps eV and sEE. It says that an object d
  exists that meets the three conditions `X.MIUnit2 d`, `X.MIid eV sEE d` and `X.AuNZ d`. The
  dossier names these conditions and shows no body for them. They are written after a dot, so
  the count of 13 definitions below `MIstar2` leaves them out.

## What the glossary shows

- `D7` and `BundleCondition` are records of data. `BundleCondition` is built over a `D7` datum,
  and the readings of the outline leave `D7` unopened in six lines.
- `RecTExists` and `UnitaryGroupThirdPlaceHypotheses` are propositions without arguments. The
  first is one statement with quantifiers. The second is a bundle of 60 named hypotheses, one
  of which is `True`.
- `LinkedAt`, `SlotNormCondition`, `BoundAtTwoThreeFamilyFonAlt`, `KPx` and `MIstar2` are
  predicates. Each says that some object exists for which further named conditions hold, and
  `KPx` adds a second condition outside its existence statement.
- `parametersOfDependence` is a function that fills the four fields of a record.
- The vocabulary is deep. Six of the ten have more than a thousand definitions below them, and
  the ten readings leave names unopened 487 times.
- `D7` is the one definition of the ten that has more than a hundred definitions below it and
  a count that was not cut at the twelfth level. The count finds 282 definitions below it on
  eight levels, and its dossier showed 42 of them.

## How the readings were made

The readings were made as in `READING.md`, by a first reader, a second reader and a check,
each a run of the command line tool Claude Code in a folder that held one dossier. The folder
of the check also held the two readings.
[`glossary.py`](glossary.py) wrote the dossiers. A dossier holds the whole text of the
definition, the number of definitions at each level below it, and the definitions of the
levels below it with their bodies, as far as 60,000 characters reach. The briefs are the three
files of [`briefs/`](briefs/) whose names start with definition.

The check found one error in the first readings, in the entry of `D7`, where one of two
formulas lacked an inverse. The model session that wrote this document corrected that
sentence, and the check then passed the entry. The check found seven errors in the second
readings of two definitions, which the entries below do not use.

## Limits

- A reading covers the text of the definition and the lower definitions that its dossier
  showed. For eight of the ten the dossier showed fewer definitions than the count finds below.
- The first reader, the second reader and the check are the same language model, so they can
  share a blind spot that the check does not find.
- A reading says what a definition is. It does not say what the definition is for in the proof.
- What a reading reports as a suggestion from the names is a guess.
- The count of definitions below a name follows the names that the declaration graph resolves.
  A definition that is reached only through a dot after a term is missing from such a count.
  The three conditions inside `MIstar2` and the condition `B.KsExact` inside `KPx` are such
  names, so the counts 13 and 71 are lower limits too.

## Files

| File | Content |
|---|---|
| `glossary.py` | writes the dossiers into `data/glossary`, which git ignores, and with `--render` the entries of this document |
| `glossary.json` | the ten readings, each with the second reading and the errors that the check found |
| `briefs/definition-reader.txt`, `briefs/definition-second-reader.txt`, `briefs/definition-check.txt` | the briefs of the three roles |

## The entries

An entry shows where the definition lies, what it is, its parts in the order of the Lean text,
the names that the reading does not open, what the names suggest, the confidence with its
reason, and what the check found.

<!-- entries -->

### `RecTExists`

The full name is `UpperTheory.Zero.LLC.RecTExists`, a def in the module Development › Automorphic Arithmetic › Foundations › Local Langlands › Is Rec T Of Is Rec. 357 or more project definitions lie below it, and the reader saw 99 of them. The reader describes it as a proposition without arguments, which is a statement and not a proved theorem.

It is the statement that, for every number field E, every algebraic closure Ω of E, every valuation subring A of Ω, every height one prime w of the ring of integers of E, and every proof h that A lies over w, there exists a map rc for which the condition IsRecT h rc holds. The map rc goes from the type the code calls IrrGL, taken over the completion of E at w, to the type the code calls WD h. IsRecT h rc says that there exist a group homomorphism a from the object called Weil h to the units of that completion, and a proof ha that a satisfies IsLocalArtin, such that the twelve laws bundled in LawsT hold for a, ha and rc. The definition only names this statement and does not prove it.

- `E Ω`. E is any type carrying a field structure that is a number field. Ω is any field that is an algebra over E and an algebraic closure of E.
- `A`. A is any valuation subring of Ω, that is, a subring that contains x or the inverse of x for every nonzero x in Ω.
- `w`. w is any element of the height one spectrum of 𝓞 E, the ring of integers of E, which is the set of its nonzero prime ideals.
- `h`. h is a proof of IsPlaceOver A w. The dossier shows this to mean that, for every x in the ring of integers of E, the valuation attached to A of the image of x in Ω is less than 1 exactly when x lies in the prime ideal w.
- `∃ rc`. The statement asserts the existence of a function rc from IrrGL over the completion of E at w to WD h. IrrGL is the type of pairs of a natural number n and an element of IrrCl of the group GL of n by n matrices over that completion, where IrrCl is a quotient of the record type IrrRep (a complex vector space with a representation marked smooth and irreducible). WD h is the quotient of pairs (n, an object of type WDRep h on ℂ^n) by the relation the code calls Iso.
- `IsRecT h rc`. This says that there exist a homomorphism a from Weil h to the units of the completion and a proof ha of IsLocalArtin h a such that LawsT a ha rc holds. IsLocalArtin has five fields named surj, cont, ord_eq, factor and glob, the first being that a is surjective. LawsT is a conjunction of twelve conditions on rc named dim, one, langlands, cusp, nu, absCentral, twist, central, dual, inj, depth and type. For example, dim says that the quantity lpDim of rc x equals the number n of x for every x, and inj says that rc x = rc y forces x = y whenever y satisfies the condition called Good.

The reading does not open the names `Weil`, `WDRep`, `WDRep.Iso`, `IrrRep.setoid`, `IsSmooth`, `Good`, `TypeLaw`, `lpDim`, `ofChar`, `WD.lpOfChar`, `lpTw`, `lpChar`, `lpDual`, `WD.lpSp`, `sumList`, `eig`, `IsCusp`, `IsCuspidal`, `nu`, `tw`, `LFactors`, `IsCosocle`, `prodIrr`, `KOne`, `IsWild`, `Ine`, `ineIncl`, `ord`, `deg`, `IsSmoothChar`, `IsGlobalArtin`, `localIdele`, `toAb`, `Ideles`, `Gab` and `smoothPart`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that this is the existence half of the local Langlands correspondence for GL_n over the completion of a number field at a finite place, with rc a reciprocity map from irreducible smooth representations to Weil–Deligne representation classes, normalised by a local Artin map a. The letter T may mark a variant of the list of laws, which the text does not explain.

The reader's confidence is medium. The quantifier structure, IsPlaceOver, IsRecT, and the field lists of LawsT and IsLocalArtin are fully visible, but many names inside those laws (such as Weil, WDRep, Good and TypeLaw) were not opened in the dossier, which reached its limit of 60,000 characters partway through level 3.

The check found no error in this reading.

### `D7`

The full name is `Formalism.BasicNotions.D7`, a structure in the module Formalism › Local Ring Cardinality › Rho Det Prime Eq Mu Tilde Mul Chi Pow. 282 project definitions lie below it, and the reader saw 42 of them. The reader describes it as a record type (a Lean structure) with 141 fields, mixing data and conditions on that data.

D7 is a record type with no parameters, and an object of it is one large bundle of data together with proofs of conditions tying the data together. It starts from a rank record R, a host record over R, a family of Hermitian spaces sp, a rows record what₂, and a family of members mem u indexed by the words of what₂ with a base word u₀. It then asks that the field what₂.LL is a totally complex number field, Galois over ℚ, with a star operation, and it adds lattice data div, a commutative group Dt with characters muTil and chiD, a record s, local theories loc, locA and locT at every prime, a chain of records nd, ntw, naut, nbc, nexp, ntypes and nth, form data fm, a measure record cd, jet data jet and extra data gx and gat. The conditions are mostly equalities and equivalences that identify pieces of one record with pieces of another, for example the two formulas that give rhoDet as the inverse of muTil (i+1) times a power of chiD with exponent −(R.N (i+1))/2, and rhoDet' as muTil (i+1) times a power of chiD with exponent (R.N i)/2. Nothing is proved here, since the structure only lists what such a bundle must contain.

- `R`. An object of the record type Ranks. The dossier shows that this holds natural numbers k, m, t with k and m even, t odd, 2 ≤ m, m + 3 ≤ k, k + m − 1 + 5 ≤ t, 3·m < t and further inequalities, on top of an unopened record Formalism.HC.Frame.
- `host`. An object of the record type Host R. The dossier shows that it extends an unopened record Formalism.HC.HostAx and adds, among much else, an embedding φ₀ of the field E into ℂ, a finite set levelPrimes, two distinct primes g 0 and g 1 in that set, and two distinct primes pde and pde' that are 1 modulo 15.
- `sp`. An object of the record type Spaces, built for R, the fields host.F and host.E and the star operation host.cmStar. The dossier shows that it holds a prime T and families X, Y, W, V of objects of type HSpace host.E, which are finite-dimensional spaces with a nondegenerate Hermitian form hT and a lattice L0, plus linear maps and rank conditions between them.
- `vol`. A function that gives a real number to every object of type HSpace host.E.
- `vol_pos`. The condition that vol W is greater than 0 for every W.
- `what₂`. An object of the record type Rows.Data R. The dossier shows that it holds a field LL with a ring map embLL into ℂ, a places record, a ring O with a map OtoLL into LL, a finite type Tau with R.f elements, a type Tup with marked elements mu0, muStar, muStar', a type Word, finite-dimensional complex inner product spaces EE, Amb μ and Mu u, and functions perCol and Bu.
- `eTau`. A bijection between the type what₂.Tau and the set that the code calls R.Psi.
- `hc`. A function that gives to each τ in Tau an object of type HCParam R. The dossier shows that such an object holds rational sequences u, v, b, e with interlacing and gap inequalities, with u taking half-integer values and v, b, e taking integer values.
- `wordFin`. The requirement that the type what₂.Word is finite, given as an instance.
- `u₀`. A chosen element of what₂.Word, used below as the base word.
- `hcW`. A function that gives an object of type HCParam R to each word u and each τ in Tau.
- `hcW_base`. The condition that hcW at the base word u₀ equals hc.
- `hcW_v`. The condition that for all u and τ the v-component of hcW u τ equals the v-component of hc τ.
- `hcW_b`. The condition that for all u and τ the b-component of hcW u τ equals the b-component of hc τ.
- `hcW_e`. The condition that for all u and τ the e-component of hcW u τ equals the e-component of hc τ.
- `hcW_first`. The condition that, when 0 < R.k, the entry of index 0 of the u-component of hcW u τ equals that of hc τ, for all u and τ.
- `hcW_last`. The condition that, when 0 < R.k, the entry of index R.k − 1 of the u-component of hcW u τ equals that of hc τ, for all u and τ.
- `mem`. A function that gives to each word u an object of type Member R what₂.Tau (hcW u). The dossier shows that a member is a triple of a column chain C, an object A of the unopened type ColumnsAtT R C, and a period map P.
- `nfLL`. The requirement that what₂.LL is a number field, given as an instance.
- `starLL`. A star operation on what₂.LL, that is an involution compatible with the ring structure, given as an instance.
- `tcLL`. The requirement that the number field what₂.LL is totally complex, given as an instance.
- `galLL`. The requirement that what₂.LL is a Galois extension of ℚ, given as an instance.
- `starLL_cx`. The condition that embLL carries the star of x to the complex conjugate of embLL x, for every x in LL.
- `div`. An object of the record type DivData what₂.LL what₂.Word. The dossier shows that it holds an object RR and a family Nu u of the unopened type HLat, linear maps Bk, real numbers h u, HH, etaF and delP with delP ≤ 1, a natural number Dall, and one inequality on HH.
- `div_good`. A conjunction of two conditions. The matrix (div.RR.X v) has invertible determinant for every v, and the matrix ((div.Nu u).X v) has invertible determinant for all u and v.
- `embE`. A ring homomorphism from the field host.E into what₂.LL.
- `embE_φ₀`. The condition that embLL composed with embE equals the embedding host.φ₀ of host.E into ℂ.
- `conjF`. An algebra homomorphism from host.E to itself over host.F.
- `conjF_eq`. The condition that conjF x equals host.conj x for every x.
- `embE_conj`. The condition that embE carries host.conj x to the star of embE x, for every x in host.E.
- `LL0`. An intermediate field between ℚ and what₂.LL.
- `hostField_le_fixedField`. The condition that embE x lies in LL0 for every x in host.E.
- `O_int`. The condition that the image in LL of every element of the ring what₂.O is integral over ℤ.
- `O_contains`. The condition that for every x in the ring of integers of host.E there is a y in what₂.O whose image in LL equals embE x.
- `plEq`. A bijection between the type what₂.places.Pl and the set of nonzero prime ideals of the ring of integers of what₂.LL (written HeightOneSpectrum).
- `val_eq`. The condition that for every w and every nonzero x in LL the value what₂.places.val w x equals vAdd (plEq w) x. The dossier shows vAdd to be minus the logarithm of the valuation at that prime, an integer.
- `ram_eq`. The condition that what₂.places.ramIdx w equals eWL of plEq w for every w. The dossier shows eWL to be the ramification index of that prime ideal over ℤ.
- `conj_val`. The condition that the value of x at the place what₂.places.conj w equals the value of star x at w, for all w and x.
- `T_level`. The condition that the number (mem u).A.T lies in the finite set host.levelPrimes for every word u.
- `T_norm`. The condition that for every word u there is an integer π of host.E that lies in host.K, satisfies π · host.conj π = (mem u).A.T, and has π − 1 in the ideal generated by the natural number host.QS · host.q · host.d · (host.g 0 · host.g 1)^2.
- `sp_T`. The condition that the prime sp.T of the spaces record equals (mem u₀).A.T, the number attached to the member at the base word.
- `cOf`. A function from words to elements of host.E.
- `cOf_ne`. The condition that cOf u is nonzero for every u.
- `cOf_eq`. The condition that cOf u · host.conj (cOf u) · (mem u).A.T equals (mem u₀).A.T in host.E, for every u.
- `T_win`. The condition that for every u the real number (mem u).A.Tstar is at most (mem u).A.T, and (mem u).A.T is at most (1 + 1/(R.f · R.k)) · (mem u).A.Tstar.
- `GamP_eq`. The condition that (mem u).A.GamP equals (mem u₀).A.GamP for every u.
- `T_ne_pde`. The condition that (mem u).A.T differs from host.pde and from host.pde' for every u.
- `Dstar_eq`. The condition that (mem u).A.Dstar equals the real number what₂.Dstar for every u.
- `clsLat`. A function that gives, for each word u, index i and element c of (mem u).C.cls i, a submodule over the ring of integers of host.E inside the space (sp.X i).V.
- `clsLat_lat`. The condition that each clsLat u i c is a full lattice over host.E, in the sense of the library predicate Submodule.IsFullLattice.
- `eMu`. For each word u, a complex linear isomorphism from the space what₂.Mu u onto (mem u).A.Mram.
- `eMt`. For each word u, a complex linear isomorphism from (mem u).P.Mt onto the space what₂.Amb what₂.mu0.
- `perCol_base_eq_PtilCol`. The condition that for all u, φ in Mu u and F in Amb mu0, the number what₂.perCol u mu0 φ F equals (mem u).P.PtilCol applied to the image of φ under eMu u, read as a function on cls 0 and Y 0, and to the preimage of F under eMt u.
- `Bu_linL`. The condition that what₂.Bu u φ F is complex linear in φ for every u and every fixed F.
- `Bu_linR`. The condition that what₂.Bu u φ F is complex linear in F for every u and every fixed φ.
- `chTw`. A function that gives, for each word u and each element of what₂.Tup, an object of type ColumnChain R what₂.Tau (hcW u). The dossier shows that a column chain holds finite types cls i, finite groups stab i c, types Y i, complex numbers rhoDet and rhoDet' of absolute value 1 below index R.m, and linear maps unf.
- `memberColumns_twistedChain_base`. The condition that chTw u at the tuple mu0 equals the column chain (mem u).C, for every u.
- `e0Tw`. For all u and μ, a complex linear isomorphism from the functions cls 0 → Y 0 → ℂ of the chain (mem u).C onto the same kind of function space of the chain chTw u μ.
- `PTw`. For all u and μ, an object of type PeriodMap R (chTw u μ). The dossier shows that a period map holds complex vector spaces Mt, Wz, Wrow and linear maps evz, lowerMap and period.
- `eMtTw`. For all u and μ, a complex linear isomorphism from (PTw u μ).Mt onto what₂.Amb μ.
- `perCol_tie`. The condition that for all u and all μ different from mu0, and all φ and F, the number what₂.perCol u μ φ F equals (PTw u μ).PtilCol applied to e0Tw u μ of the image of φ under eMu u, and to the preimage of F under eMtTw u μ.
- `jEE`. A map from div.RR.V into what₂.EE that is additive and semilinear along embLL, meaning that scalars from LL act on the target through embLL.
- `jEE_basis`. The condition that the images under jEE of the vectors div.RR.b i are linearly independent over ℂ and span all of EE.
- `jN`. For each u, a map from (div.Nu u).V into what₂.Mu u that is semilinear along embLL.
- `jN_basis`. The condition that for each u the images under jN u of the vectors (div.Nu u).b i are linearly independent over ℂ and span all of Mu u.
- `Dall_eq`. The condition that the natural number div.Dall equals what₂.Dall.
- `delP_eq`. The condition that the real number div.delP equals what₂.delp.
- `Dt`. A type, with no further description at this point.
- `instDt`. A commutative group structure on Dt, given as an instance.
- `detCls`. A function that gives an element of Dt to each u, i and element of (mem u).C.cls i.
- `muTil`. For each natural number, a group homomorphism from Dt to the nonzero complex numbers.
- `chiD`. A group homomorphism from Dt to the nonzero complex numbers.
- `UO`. A subgroup of Dt.
- `chiD_UO`. The condition that chiD takes the value 1 on every element of UO.
- `e1Dt`. A group homomorphism into Dt from the unitary elements of host.E, that is the elements whose product with their star is 1.
- `rest_detCharacter_on_unitary_eq`. The condition that for every unitary z in host.E the complex number chiD (e1Dt z) equals the product over τ in Tau of the inverse of host.emb (eTau τ) z.
- `relDet`. A function that gives, for each N and each pair of objects of type SDLat host.E N, an element of the quotient group Dt / UO. The dossier shows SDLat E N to be the submodules of E^N over the integers of E that satisfy an unopened condition IsSDLat.
- `relDet_self`. The condition that relDet N L L equals 1 for all N and L.
- `relDet_mul`. The condition that relDet N L L' · relDet N L' L'' equals relDet N L L'' for all N, L, L', L''.
- `relDet_smul`. The condition that whenever L' is the image of L under a unitary N by N matrix γ over host.E, relDet N L L' equals the class in Dt / UO of e1Dt applied to the determinant of γ.
- `rhoDet_eq_inv_muTilde_chiD_pow`. The condition that for all u, i and c in (mem u).C.cls i, the number (mem u).C.rhoDet i c equals the inverse of muTil (i+1) (detCls u i c) times chiD (detCls u i c) raised to the power −((R.N (i+1))/2), with the division taken in the natural numbers.
- `rhoDetPrime_eq_muTilde_mul_chi_pow`. The condition that for all u, i and c in (mem u).C.cls (i+1), the number (mem u).C.rhoDet' i c equals muTil (i+1) (detCls u (i+1) c) times chiD (detCls u (i+1) c) raised to the power (R.N i)/2, with the division taken in the natural numbers.
- `dsig`. A function from what₂.Tau to the real numbers.
- `dsig_pos`. The condition that dsig ρ is greater than 0 for every ρ.
- `s`. An object of the type that the code calls Formalism.MainNotions.S.Draft.SData, built for R, host.F, host.E, conjF, the words, Tau and hcW. Its body is not in the dossier.
- `s_split`. The condition that for every p the optional value (s.atP p).split is present exactly when the number that the code calls Loc.resChar p is one of the two primes host.g 0 and host.g 1.
- `s_HH`. The condition that the complex dimension of the space s.HH equals what₂.Dall.
- `s_Cu`. For each u, a complex linear isomorphism from s.Cu u onto (mem u).A.Mu0.
- `s_PlF`. A bijection between s.PlF and the set of nonzero prime ideals of the ring of integers of host.F.
- `loc`. An object of type LocTheory. The dossier shows this to be a choice, for every prime l, of an object of the unopened type LocPrime l.
- `locA`. For every prime l, an object of type LocAinf l (loc l). The dossier shows that this holds group actions actC and actT, a sequence ζ n with ζ 0 = 1, ζ (n+1)^l = ζ n and ζ 1 ≠ 1, an element ε, and an injective ring map ιA from Ainf l into the ring (loc l).R.B with compatibility conditions.
- `locT`. For every prime l, an object of type LocTied l (loc l) (locA l). The dossier shows that this holds ring isomorphisms eB and eD from the rings (loc l).R.B and (loc l).R.BdR onto rings that the code calls Per.Bcris l and Per.BdR l, with conditions that they respect the group actions, a map φB, filtrations and the map ιA.
- `nd`. An object of type NData R host what₂. The visible part of its body holds an algebraic closure Om of host.E, an index type Loc with a prime l i, an index j i between 1 and R.m, a place w i, complete discrete valuation rings O i that are finite over the l i-adic integers, finite sets X i, modules Mt i and characters chi i c.
- `ntw`. An object of type NTw R host what₂ LL0 nd. The visible part of its body holds a ring automorphism cc of nd.Om, an index type Tw with primes l i, discrete valuation rings O0 i, O i and Ok i k, embeddings of LL0, and characters delta i whose inertia images have exactly 15 elements at the places in pD i.
- `naut`. An object of type NAut nd. The visible part of its body holds field maps iotaQ and iotaQC, and for each place w a type LP w with a dimension lpDim, a sum lpSum, a twist lpTw, predicates unr, mono0 and tempered, a multiset frobEig, and laws relating them.
- `nbc`. An object of type NBC naut. The dossier shows that it holds types AU j and Wt j with multisets satAU of size R.nV / 2 and infW of size R.nV, and injective maps embAV from naut.AV i into AU (nd.j i) that respect the local data.
- `nexp`. An object of type NExp R host what₂ LL0 nd ntw. The visible part of its body holds finite-dimensional spaces Fm i j b with an action of the group G0g nd, central idempotents eAlg i b in a group algebra, a function eLL0 from G0g nd to LL0, and homomorphisms delU with conditions.
- `ntypes`. An object of type NTypes naut. The visible part of its body holds a number field Mray that is Galois with commutative Galois group over host.K, multisets bc σ of pairs with the products summing to R.r, homomorphisms rbar into GL of size R.r, elements tg k v of inertia groups, and central orthogonal idempotents eSer.
- `nStage_trivialCharacter_compat`. A condition that the code calls ntypes.IdempotentMatchesAction. Its body is not visible in the dossier.
- `nStage_trivialCharacter_coeff_eq`. The condition that for every g in G0g nd the image under embLL of nexp.eLL0 g equals the coefficient at g of ntypes.e0. The dossier shows G0g nd to be the families of invertible R.r by R.r matrices over the integers modulo host.g k, indexed by pairs of k in {0, 1} and an element of nd.PlG k.
- `nth`. An object of type NTh R host what₂ LL0 nd ntw nexp. The visible part of its body holds ring maps iC into the l-adic complex numbers, numbers aL i equal to 1 when ntw.l i is one of host.g k and 0 otherwise, injective evaluation maps ev, polynomial sets Harm cut out by second-order differential conditions, and maps thV, recDet and actK.
- `nbr`. For each i in nd.Loc and each prime w of host.E containing nd.l i, an object of type LocBridge. The dossier shows that this holds a field map j from nd.Om into Om l, a group isomorphism e that is continuous in both directions from the group that the code calls Dec at w onto GK Kw, and a ring isomorphism eO from nd.O i onto OL LL.
- `nbr_ind`. The condition that for all such i and w an element x of nd.Om lies in nd.plOm.1 w exactly when the norm of its image under the map j of nbr i w is at most 1.
- `self_good`. The condition GoodCoef host.condN on the field LL of each bridge nbr i w. The dossier shows GoodCoef N LL to say that every x in Om l with x raised to the least common multiple of l and N equal to 1 lies in LL.
- `ntwbr`. For each i in ntw.Tw and each prime w of host.E containing ntw.l i, an object of type LocBridge of the same kind as nbr, now with the ring ntw.O0 i.
- `ntwbr_ind`. The condition that for all such i and w an element x of nd.Om lies in nd.plOm.1 w exactly when the norm of its image under the map j of ntwbr i w is at most 1.
- `loc_tie`. The condition LocTie nd naut loc nbr. The dossier shows that it asks, for every i and w, that a map iotaOQ agrees with the bridge map toLL, and that the predicates IsCrysW, IsdRW, IsPotCrysW and the multiset jumpsW of naut agree with the corresponding predicates and multiplicities of the bridge computed in loc, for continuous matrix representations over nd.O i and over larger fields LL'.
- `bc_tie`. The condition BcTie nd naut ntypes. The dossier shows that it asks that whenever a list Sig satisfies the unopened condition HasParamW and two further conditions on its entries, the multiset ntypes.bc σ equals the multiset of pairs (a, d) read off from Sig.
- `rbar_tie`. The condition RbarTie nd naut ntypes. The dossier shows that it asks, under the unopened conditions HasParamW and IsRepOfSig, that ntypes.rbar σ (nd.w i) satisfies the unopened condition IsSSRep and has, for every group element, the same characteristic polynomial as the reduction of ρ modulo the maximal ideal of nd.O i, after moving both to a common field.
- `mtpar_tie`. The condition MtParTie nd naut ntypes. The dossier shows that it asks that ntypes.MtPar (nd.mu i) (nd.j i) σ' equals the supremum of the submodules naut.typeV i P over those P that satisfy a condition built from the unopened names isoLoc, IsBCV, twistIso and muPart.
- `Z_tie`. The condition that for all i the finite set nd.Z i has the same elements as the set ZN nd naut i. The dossier shows ZN to be the set of x that arise as naut.ptV i P for some P that satisfies the unopened condition IsBCV with a parameter list containing one named entry.
- `Zgood_tie`. The condition that for all i the finite set nd.Zgood i has the same elements as ZgoodN nd naut i. The dossier shows ZgoodN to be the elements x of ZN for which some Sig satisfies the unopened conditions HasParamX and goodSig.
- `etaJ_tie`. The condition that for all j with 1 ≤ j ≤ R.m and all w, the quantity what₂.etaJ j w equals the sum of nd.etaLoc i over i in the finite set nd.locs j w. The dossier shows that nd.locs j w consists of the i with nd.j i = j and nd.w i = w.
- `fm`. For each word u, an object of type MemberForms built for what₂.LL, embLL, the places record, Tau, hcW u and the three components of mem u. The visible part of its body holds modules lv and lk of rank R.N i, maps dil with a group-action law, weights lam, subspaces Fi with Fi 0 = A.Mu0, forms ipV, objects lat i of type HLat and semilinear maps emb i.
- `eMu_isom`. The condition that for all u and all φ, ψ in what₂.Mu u, the inner product of φ and ψ equals (fm u).ipC 0 applied to their images under eMu u, read as functions on cls 0 and Y 0.
- `nuIn`. For each u, a linear map over what₂.LL from (div.Nu u).V into ((fm u).lat 0).V.
- `nuIn_inj`. The condition that nuIn u is injective for every u.
- `nuIn_range`. The condition that the image of nuIn u equals the submodule (fm u).ramSub for every u.
- `nuIn_jN`. The condition that for all u and x the image of jN u x under eMu u, read as a function on cls 0 and Y 0, equals (fm u).emb 0 applied to nuIn u x.
- `nuIn_norm`. The condition that for all u, v and x the real number normAt computed in (div.Nu u) at v on x equals normAt computed in (fm u).lat 0 at v on nuIn u x. The dossier shows normAt to be cnorm of fcoord, two names it does not open.
- `jEE_norm`. The condition that for every x in div.RR.V the number normAt of x in div.RR, taken at the infinite place given by embLL, equals the norm of jEE x in EE.
- `s_Cu_isom`. The condition that for all u and all x, y in s.Cu u, the inner product of x and y equals (fm u).ipC 0 applied to their images under s_Cu u, read as functions on cls 0 and Y 0.
- `sEE`. A map from what₂.EE to s.HH that preserves norms and is conjugate-linear over ℂ, as the starred arrow in the Lean text indicates.
- `cd`. An object of type CDHaar. The dossier shows that it holds, for all natural numbers P and Q, a Haar measure on a space that the code calls UpqT P Q, that the measure for (N, 0) is a probability measure, and that for all P and Q some constant c, neither 0 nor infinite, satisfies the unopened condition OmegaDensity for both (P, Q) and (P + Q, 0).
- `jet`. An object of type ThetaJet R host. The dossier shows that it holds index types Sit and Sit1, local objects loc i and loc1 i of the unopened types JetLoc and JetLoc1, indices jOf i and j1Of i between 1 and R.m, and conditions that the numbers N0 and N1 of each local object equal R.N at the index minus one and at the index.
- `jetU`. A function from jet.Sit to the words of what₂.
- `jetL`. For each i in jet.Sit, an element of the class set (mem (jetU i)).C.cls (jet.jOf i − 1).
- `jetL'`. For each i in jet.Sit, an element of the class set (mem (jetU i)).C.cls (jet.jOf i).
- `jetW`. A function from jet.Sit to what₂.places.Pl.
- `jetW_l`. The condition that what₂.places.resChar (jetW i) equals the number (jet.loc i).l for every i.
- `jetTau`. For each i in jet.Sit, a function from the integers modulo (jet.loc i).d to what₂.Tau.
- `jetW1`. A function from jet.Sit1 to what₂.places.Pl.
- `resChar_thetaJetPlaceDegOne`. The condition that what₂.places.resChar (jetW1 i) equals the number (jet.loc1 i).l for every i in jet.Sit1.
- `jetTau1`. A function from jet.Sit1 to what₂.Tau.
- `jetU1`. A function from jet.Sit1 to the words of what₂.
- `jetL1`. For each i in jet.Sit1, an element of the class set (mem (jetU1 i)).C.cls (jet.j1Of i − 1).
- `jetL1'`. For each i in jet.Sit1, an element of the class set (mem (jetU1 i)).C.cls (jet.j1Of i).
- `gx`. An object of type GlobalExtra what₂.LL what₂.Tau. The dossier shows that it holds a positive real number Om τ s for each τ and each embedding s of LL into ℂ, and a positive real number thOne s for each such embedding.
- `gat`. For each word u and place w such that GIdx host (mem u).A.T p holds for p = what₂.places.resChar w, an object of type GAtP p. The dossier shows GIdx to say that p is prime, 5 ≤ p, host.cls p is the value inertClass, the unopened condition HNeZero host p holds, p is not in host.levelPrimes and p does not divide T. It shows GAtP p to hold a discrete valuation ring O, a field Kf, a finite type comp with levels, and a number e.
- `gat_d`. The condition that the number (gat u w h).d equals the complex dimension of (mem u).A.Mu0, for all u, w and h. The field d is not among the fields of GAtP that the dossier shows.
- `Y_sigval`. The condition that for every j ≤ R.m and every embedding τ of host.E into ℂ, the pair (sp.Y j).sig τ equals sigYD R j. The dossier shows sigYD R j to be the pair (R.rankY j − (R.m − j)/2, (R.m − j)/2) of natural numbers.

The reading does not open the names `Formalism.HC.Frame (and R.f, R.N, R.Psi, R.GG, R.r, R.nV, R.rankY, R.sigW, R.ord)`, `Formalism.HC.HostAx and its raw part (host.F, host.E, host.K, host.conj, host.cmStar, host.emb, host.gal, host.cls, host.QS, host.q, host.d, host.condN)`, `ColumnsAtT (and A.T, A.Tstar, A.GamP, A.Dstar, A.Mram, A.Mu0)`, `PeriodMap.PtilCol`, `Rows.Places (Pl, val, ramIdx, conj, resChar)`, `the cut tail of Rows.Data (including etaJ and shaLen)`, `HLat (V, b, X, L, Good)`, `OLat`, `IsSDLat`, `CMData`, `HSpace.SigOK, HSpace.IsDefinite, HSpace.IsIsomEmb`, `Formalism.MainNotions.S.Draft.SData (atP, split, HH, Cu, PlF)`, `Formalism.MainNotions.S.Loc.resChar`, `LocPrime`, `FinExt, Om, GQ, GK, OL, Ainf, OC, OCb, PadicComplex, Qbar`, `Per.Bcris, Per.BdR, Per.IsCrisDR, Per.IsLog and the other Per names`, `ReciprocityTheory.Gal.Dec, Ine, G`, `NTypes.IdempotentMatchesAction and NTypes.e0`, `the cut tails of NData, NTw, NAut, NExp, NTh, NTypes and MemberForms (including etaLoc, PlG, AV, ptV, typeV, ipC, ramSub)`, `HasParamW, HasParamX, goodSig, IsRepOfSig, IsSSRep, IsBCV, isoLoc, twistIso, muPart, iotaOQ, mapRep`, `LocBridge.IsCrysW, IsdRW, IsPotCrysW, IsJumpW, multW and their E variants`, `HNeZero`, `OmegaDensity, UpqT`, `JetLoc, JetLoc1`, `cnorm, fcoord, majAt`, `Formalism.MainNotions.G.Places, Level, and the field d of GAtP` and `Formalism.GaloisCohomology.Places, LData, shaLen`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. As a suggestion only, the names point to a global arithmetic setup around a CM field E over a totally real field F, with Hermitian spaces and unitary groups, a tower of automorphic forms on class sets linked by theta-type period maps, Galois representations with crystalline and de Rham conditions tied to p-adic period rings, and Hecke data at auxiliary primes. The name D7 and the module name suggest that this is the seventh layer of a staged data package whose newest addition is the pair of determinant-character formulas for rhoDet and rhoDet'.

The reader's confidence is medium. The whole text of D7 and the bodies of most level-one records are visible, but several of those bodies are cut off and many conditions rest on names from deeper levels (such as ColumnsAtT, HostAx, Frame, Places, HLat and SData) that the dossier does not open.

The check found one error in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- In the field "says" reading A states that the two formulas give "rhoDet and rhoDet' as muTil(i+1) times a power of chiD", whereas the Lean text gives rhoDet as the inverse "(muTil (i + 1) (detCls u i c))⁻¹" times the power of chiD, and only rhoDet' uses muTil (i + 1) itself.

### `UnitaryGroupThirdPlaceHypotheses`

The full name is `GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses`, a structure in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Bernstein Unitary Product Irreducible. 2,189 or more project definitions lie below it, and the reader saw 92 of them. The reader describes it as a record type whose 60 fields are all propositions, so it is itself a proposition (a bundle of hypotheses).

This is a structure in Prop with 60 fields, and each field is a proof of one named proposition. It therefore states the conjunction of those 60 propositions, with no parameters and no quantifiers of its own. Fifty-six of the fields are single named statements, most of them in a namespace called Published, and the dossier shows a body for each of these, although most bodies rest on conditions that are not opened. Three fields (litN, toHypothesesX, nLink) are themselves smaller bundles, and one field (siegelEisensteinSimplePole) has a type that unfolds to True and so asserts nothing. Several statements occur more than once, directly and again inside the sub-bundles.

- `clozelCohomological`. For every totally complex number field E, every natural number a with 1 ≤ a, and every π of the type the code calls CuspSub E a, if CG.mk π satisfies the condition called IsRegAlg then π satisfies the condition called GKCoh.IsCohomological. Those two conditions are not opened.
- `greenCuspidal`. A proof of the proposition that the code calls GlobalTheory.GLq.Green. Its body is not shown.
- `heckeLAdicCharacter`. For every number field E with algebraic closure Ω there is a group homomorphism art from Ideles E to Gab E Ω that satisfies IsGlobalArtin, and such that for every prime l, every ring isomorphism ι from Qbar l to the complex numbers, every χ of type HChar E and every integer-valued function n on the embeddings of E into ℂ with IsAlgPos χ n, there is exactly one continuous homomorphism r from G E Ω to the units of Qbar l with IsLAdicOf art ι χ n r. The named conditions are not opened.
- `chebotarevDegreeOne`. For a number field F with algebraic closure Ω, a finite Galois intermediate field L, an automorphism g of L over F and a finite set S of nonzero primes of the ring of integers of F, there is a prime v outside S with inertia degree 1 over ℤ, together with a valuation subring B of Ω with IsPlaceOver B v whose group Ine B lies in the subgroup fixing L, and an element σ of G F Ω with IsFrob B (normV v) σ whose restriction to L is g. IsPlaceOver, Ine and IsFrob are not opened.
- `galoisRepOfPolarizedCuspidal`. The proposition UpperTheory.GalS.CuspUAlt. For every field E carrying the unopened class IsCMField, algebraic closure Ω, prime l, isomorphism ι from Qbar l to ℂ, a ≥ 1, π in CuspSub E a and χ in HChar of the maximal real subfield of E, if CG.mk π is IsRegAlg and IsPolarized π χ holds, then there exist a homomorphism r from G E Ω to GL of size a over Qbar l, an integer wt and a function HT from embeddings of E into Qbar l to multisets of integers with the unopened condition IsGalUAlt π χ ι r wt HT.
- `baseChangeDefiniteUnitary`. An abbreviation for UpperTheory.BaseChangeIdentities.DefiniteN. For every IsCMField E in which every prime w satisfies Algebra.IsUnramifiedAt over the integers of the maximal real subfield, every n ≥ 1 and every submodule π of complex functions on UA E n with IsAutRepU π, there exist a number c, sizes N i summing to n, submodules V i of Sm E (N i), local objects σ and multisets m with the unopened condition IsBaseChangeU π h V σ m.
- `bhattScholzeCrystallineLattices`. For a prime l, K in FinExt l (a finite-dimensional intermediate field over the l-adic numbers), and data P₀, e with IsAinf K P₀ e, a conjunction of two statements holds. The first says that under IsStd P AI every lattice T with IsCrys admits an object E of type FCrys and a semilinear map j satisfying Realises, and the second says that any linear map f commuting with the two actions between two realised modules comes from exactly one u of type FHom E E' compatible with j and j'. IsAinf, IsStd, IsCrys, Realises and FCrys are not opened.
- `heckeLAdicCharacterAbove`. A proof of the proposition that the code calls GlobalTheory.TripleGal.CharAbove. Its body is not shown.
- `cuspRapidDecay`. For every D of type D7, every family θ with IsInfFam θ, every V of type HSp D with e satisfying IsExpFam, and every complex function φ on GA D V satisfying IsAutFun, IsSmoothInf, IsUnifModerate and IsCuspFun, the condition CuspDecay.IsRapidDecay θ V φ holds. All of these conditions are unopened.
- `weilSiegelFormulaUnitary`. For D of type D7, A and B of type HSp D, a Haar measure m on GA D B, 1 ≤ A.rank, and either wittIdx B = 0 or A.rank + wittIdx B < B.rank, two things hold. First, a seminorm ν with IsContSeminorm bounds absThetaInt. Second, for every ω with IsWeilDatumO ψ (dblSp A) B 1 χ ω and every f with IsThetaFunO, a descended function is integrable and, when 2 * A.rank < B.rank, a coset sum over siegel A in GQ (dblSp A) of the section swSection converges in the sense CosetConv and equals the average of that descended function. The named objects are unopened.
- `siegelWeilUnitaryConvergent`. For D of type D7 and A, B of type HSp D with A.rank < B.rank, B.rank ≤ 2 * A.rank and A.rank + wittIdx B < B.rank, and under a list of unopened conditions (IsWeilDatumO, IsMaj, HasIwasawa, IsInfFam, IsCartanInv, a commutation condition, IsCovolOne, Haar measure, IsFockVec), a descended function built from thetaKO is integrable for every g, and the unopened relation Eis.EisValueAt holds between a section at the point sZero A B and thetaMean ω ν f.
- `doublingMethod`. An abbreviation for the proposition that the code calls ResidueKilled.DM. Its body is not shown.
- `unramifiedDoublingGL`. For a nonarchimedean local field k of characteristic zero, a Haar measure μ on GL of size n over k giving the subgroup KO measure 1, a representation π with HasSatake π α and a function ω with IsZonal, there is a real s₀ such that for every complex s with real part above s₀ the function sphSection times ω is integrable and its integral equals lFactor (resCard k) α (s + 1/2) times lFactor (resCard k) α⁻¹ (s + 1/2) times invNormFactor (resCard k) n s. HasSatake, IsZonal, sphSection, lFactor and invNormFactor are unopened.
- `bernsteinZelevinskyFiniteness`. For every nonarchimedean local field k, the conjunction of four statements called IrreducibleAdmissible, JacquetFiniteLength, InductionFiniteLength and InductionContragredient. Their bodies are shown and say that smooth irreducible complex representations of GL n k are IsAdmissible, that jac and parInd preserve HasFiniteLength for smooth representations, and that there is an equivalence between parInd of contra ρ and contra of parInd ρ given by an integral over KO, where IsAdmissible, HasFiniteLength, jac, parInd and contra are unopened.
- `formalDegreeCompactDual`. For cd of type CDHaar and scale factors sc n ε that make the scaled measures muG match cd under every reindexing, and for every strictly decreasing lam with lam a − (N − 1)/2 an integer, every σ with the unopened condition IsDS ε lam σ and every nonzero w, the quotient of ‖w‖ to the power 4 by the integral of the squared absolute value of the inner product of w with σ(g)w equals the product over a < b of |lam a − lam b| divided by the product over a < b of (b − a).
- `bernsteinUnitaryProductIrreducible`. For a nonarchimedean local field k and complex representations π₁ of GL r k and π₂ of GL t k that are each smooth (every vector has open stabiliser), irreducible and unitarisable (they preserve a positive definite Hermitian form), the representation prod₂ π₁ π₂ is irreducible. The body of prod₂ is shown as ind₂ applied to extTensor π₁ π₂, and ind₂ and extTensor are unopened.
- `geometricLemmaFiltration`. For every nonarchimedean local field k, the condition that the code calls GlobalTheory.SmGL.JacquetOfInducedFiltration k. That condition is not opened.
- `unlinkedProductIrreducible`. For π₁ in Irr k r and π₂ in Irr k t with IsCuspSupport data σ and σ', if no σ a is equivalent to a twist of any σ' b of the same size by detChar of unrChar k α for a nonzero complex α, then prod₂ π₁.π π₂.π is irreducible. Irr, IsCuspSupport, twist, detChar and unrChar are unopened.
- `depthZeroJacquetInjective`. For π in Irr k n and a vector v fixed by the join of KOne k with the intersection of unipRad k e and KO k, if the class of v in the quotient Jacquet π.π (unipRad k e) is zero then v is zero. KOne, KO, unipRad and Jacquet are unopened.
- `jacquetShalika`. The conjunction of two propositions that the code calls JacquetShalikaRigidity and JacquetShalikaBound. Neither body is shown.
- `automorphicFormsFiniteGL`. For a totally complex number field E, an open subgroup L of GL of size a over the finite adele ring of E, a finite-dimensional complex representation ρ of Kinf E a (a unitary matrix group over Cinf E) whose matrix coefficients are continuous, and any function c, the complex span of the set forms L ρ c is finite-dimensional. The set forms is shown as those φ with IsAutForm that are fixed by L, have coefficients in AutFin.coeffSpan ρ and satisfy cap τ u φ = c τ u • φ, where these inner names are unopened.
- `localGlobalAboveL`. The proposition UpperTheory.GalS.CarUAlt. For an IsCMField E, a prime l, an isomorphism ι, a ≥ 2 and π in CuspSub E a with π.IsCsd and CG.mk π IsRegAlg, there exist r, wt and HT with IsGalUAlt π (quadChar E ^ a) ι r wt HT such that at every prime w in placesOver E l, for every σ with π.IsLocComp w σ and every rc with IsRecT h rc and NcW (rc (algNorm σ)), the relation Ab holds between wdAt of r restricted to the subgroup Dec A and rc (algNorm σ). All of these conditions are unopened.
- `regularAlgebraicPurity`. For an IsCMField E, a ≥ 1 and π in CuspSub E a with CG.mk π IsRegAlg, there is an integer w₀ such that for every embedding τ of E into ℂ the multiset infChar at the complex conjugate of τ equals infChar at τ with each entry z replaced by w₀ − z, and also GKCoh.IsCohomological π holds.
- `globalArtinReciprocity`. For every number field E with algebraic closure Ω there exists a group homomorphism art from Ideles E to Gab E Ω with the unopened condition IsGlobalArtin art.
- `heckeLAdicParameterAbove`. The proposition HeckeLAdicParameterAboveAlt. For art with IsGlobalArtin, χ and n with IsAlgPos χ n, and a continuous μ with IsLAdicOf art ι χ n μ, at every prime w with local data A, Bw, ξ satisfying IsPlaceOver, Pst.Induces and NPin.IsComp χ w ξ, and every rc with IsRecT h rc, the object wdAt of (rk1 μ) restricted to Dec A equals rc applied to the class of Irr.ofDet 1 ξ. All these names are unopened.
- `deRhamPotSemistable`. For a prime l with P and AI such that LocTied l P AI is nonempty, K in FinExt l, and a finite-dimensional l-adic representation ρ of the subgroup GK K (the subgroup fixing K) with continuous orbit maps, the condition IsDR (P.PD K) ρ implies the condition IsPst P ρ. IsDR and IsPst are unopened.
- `harishChandraFinite`. For D of type D7, θ with IsInfFam, V of type HSp D, an open subgroup U of GA D V, data ε and fr with IsFrameFam, finite-dimensional representations ρ τ with IsContRep, and any c, the complex span of the set forms θ V U ε fr ρ c is finite-dimensional. This set forms and the conditions are unopened.
- `greenRegularCharacters`. For a prime g, d > 0 and a field K of dimension d over the integers mod g, there is a map τ from characters θ of the units of K to complex functions on Gn g d such that for θ with IsRegularChar the function τ θ is IsCusp, has value at 1 equal to the product over i from 1 to d − 1 of (g^i − 1), and at y with irreducible characteristic polynomial having a root z in K has value (−1)^(d−1) times the sum over i < d of θ(z^(g^i)). Also τ θ = τ θ' exactly when θ' = θ^(g^i) for some i < d, and every IsCusp function is τ θ for some regular θ, where Gn, IsRegularChar and IsCusp are unopened.
- `zelevinskyPolynomialRing`. For every nonarchimedean local field k there exist a family Z assigning to each Δ of type Segment k an element of IrrCl of GL of size Δ.len * Δ.d, and an additive isomorphism Ψ from GrothGL k to the polynomial ring over ℤ in variables indexed by Segment k, with IsSegmentClass k Z, IsProductIso k Ψ and Ψ sending the generator of Z Δ to the variable X Δ. Segment, IrrCl, GrothGL and the two conditions are unopened.
- `rayClassFieldSt`. A proof of the proposition that the code calls GlobalTheory.NT.RayField. Its body is not shown.
- `rayCharacterArtin`. For a number field F, a nonzero ideal 𝔪 of its integers and a homomorphism f from idealsPrimeTo 𝔪 to a commutative group A that is trivial on principal ideals generated by x with x − 1 in 𝔪, there is a homomorphism φ from G F Ω to A with open kernel, trivial on Ine B at primes not dividing 𝔪, sending every σ with IsFrob at such a prime v to f of primeElt 𝔪 v, with a stated description of the image of Ine B at primes dividing 𝔪, and φ is the only open-kernel homomorphism with that Frobenius property.
- `genericUnitaryDualGL`. For a nonarchimedean local field k of characteristic zero, every smooth, irreducible, unitarisable complex representation π of GL N k that satisfies IsGeneric also satisfies GenericUnitary.IsComplementaryProduct. Those last two conditions are unopened.
- `standardCosocleGL`. For a nonarchimedean local field k of characteristic zero, a multiset 𝔪 of Segment k and a family x of h elements of IrrGL whose sizes sum to N with LFactors 𝔪 x, there exists π of type IrrRep (GL N k) with IsCosocle π.ρ (prodIrr x hd). LFactors, IsCosocle and prodIrr are unopened.
- `cheb`. The proposition GlobalTheory.TwSys.Cheb. For a number field F, an open normal subgroup U of G F Ω, an element g and a finite set A of primes, there is a prime v outside A with inertia degree 1 and ramification index 1 over ℤ, a valuation subring B with IsPlaceOver B v and Ine B inside U, and σ with IsFrob B (normV v) σ and σ g⁻¹ in U.
- `discreteSeriesCover`. For natural numbers p, q with 1 ≤ p + q and T of type GrpData p q, there is a map D from rational-valued functions lam on Ix p q with IsParam lam to DSRep T such that every D lam satisfies HasTypes (D lam) lam and every R in DSRep T satisfies UnitEquiv R (D lam) for some lam. These names are unopened.
- `harishChandraModules`. The conjunction of two statements. The first is that HarishChandraModulesOn T holds for all p, q with 1 ≤ p + q and all T of type GrpData p q, and the second is the proposition called KFiniteAnalyticUJ, and neither inner name is opened.
- `casselmanWallach`. For σ on a complex Hilbert space H with IsURepOn and IsIrredOn for UJset ε, a complete Hausdorff space E with seminorms p and maps π, dπ satisfying IsSmoothModRep, and a linear map T₀ with IsGKMap, there is a linear map T agreeing with T₀ on vectors with IsKFin, satisfying IsSmoothGMap, unique on the vectors with SmoothVec among such maps, with closed image of those vectors, and, if T₀ is nonzero on some IsKFin vector, with each sobNorm bounded by a continuous seminorm of T w. The named conditions are unopened.
- `weilRepresentationUnitaryPair`. For D of type D7, an additive character ψ with IsStdChar D ψ (−1), S and T of type HSp D, and circle-valued characters χS, χT with IsHeckeChar and ResEta conditions for S.rank and T.rank, there exists a homomorphism ω from GA D S × GA D T to linear endomorphisms of the complex functions on WO S T with IsWeilDatumO ψ S T χS χT ω.
- `discreteSeriesExists`. Defined to be the proposition that the code calls DiscreteSeriesUpqExists. Its body is not shown.
- `discreteSeriesClassification`. For every n there is a family of inner product spaces H ε lam with maps π ε lam such that, for strictly decreasing lam with lam a − (n − 1)/2 an integer, the space is complete and nontrivial with IsURepOn, IsIrredOn, IsSqIntOn and HasInfChar, has a unique submodule with IsKTypeOf for lam + rhoN ε − rhoC ε, and every other IsKTypeOf parameter μ differs from that one by a natural-number combination of root a b with a < b. Conversely every complete nontrivial σ with those three conditions is carried, after a permutation s and for some such mu, by a linear isometry onto H (ε ∘ s) mu that intertwines the actions.
- `strongApproxSU`. For number fields F, E with σ satisfying IsCMExt F E σ, M ≥ 2, J with IsHermND σ J and ε with IsPlacesIdem S₁ S₂ ε, if SUSupp σ J ε is not compact then every g in SUAdelic σ J lies in the closure of the set of products γ * h with γ in SURat σ J and h in SUSupp σ J ε. These names are unopened.
- `siegelWeilUnitaryConvergent2`. A second statement with the same short name, from the namespace HeckeCharacterZeroLocus.SiegelWeilU. It says that for number fields F, E with IsCMExt F E σ and every M and J with IsHermND σ J, the unopened condition SiegelWeilAt F E σ M J holds.
- `harishChandraAnalyticity`. The conjunction of two propositions that the code calls AdmissibleCoefficientsAnalytic and LeviSubmoduleDense. Neither body is shown.
- `cuspTraceClass`. For D of type D7, V of type HSp D and a right-invariant Haar measure μ on GA D V, every f in CcGA V gives an operator RcuspOp V μ f satisfying IsTraceClass. These names are unopened.
- `dixmierMalliavinFactorisation`. For a topological group G with a homomorphism ι into n by n complex matrices whose map to GL n ℂ is a closed embedding, a Haar measure μ, a neighbourhood V of the identity and f in CcMat ι, there are finitely many functions g i and h i in CcMat ι, with the support of g i inside V and the support of h i inside the support of f, such that f is the sum of conv μ (g i) (h i). CcMat and conv are unopened.
- `flathFactorisation`. For IsCMExt F E σ, J with IsHermND σ J and a homomorphism π from GAd σ J to bounded operators on H with IsIrrUnitary π, there exist local objects R v of type IrrU (GPl σ J v), vectors ξ v and a map B with Flath.IsUnramFactorisation R ξ π B. These names are unopened.
- `cMCurveGoodOutsidePrimeSt`. For every prime p with p mod 4 = 3 and 3 < p there exist a subfield F of ℂ that is a number field and a Weierstrass curve A over F with IsGoodCMCurve p F A and HasMinimalDiscriminant A (−p^3). Those two conditions are unopened.
- `weberRayFieldSt`. For a totally complex number field K inside ℂ of degree 2 over ℚ with discriminant less than −4, a period pair L whose lattice is exactly the image of the ring of integers of K, and n > 0, the field obtained by adjoining weberSet L n to K is a number field, satisfies IsAbelianGalois over K, and satisfies IsRay for the ideal generated by n. weberSet, IsAbelianGalois and IsRay are unopened.
- `discreteSeriesCoverExists`. For all p, q, every T of type GrpData p q and every rational-valued lam on Ix p q with IsParam lam, there exists R in DSRep T with HasParam R lam.
- `siegelWeilUnitarySchrodinger`. For D of type D7, n and V with n < V.rank, V.rank ≤ 2 * n and n + wittIdx V < V.rank, and under unopened conditions on ψ, χ, θ, μ, ω, H, l, s, ν and Φ, three things hold. A descended theta function is integrable for every g, for every complex z with real part above n/2 the section sect ω H Φ z is LeftInv and satisfies Eis.CosetConv, and for every g the relation HolValueAt holds between the coset sum as a function of z, the point s0 V n and thetaInt ω ν Φ g.
- `siegelEisensteinContinuation`. For D of type D7, V with 0 < V.rank, a with IsMaj V a and HasIwasawa, μ with IsHeckeChar and ResEta D μ b, a complex s₁ and φ in degPS V a μ s₁, the condition EisContinues V (flat V a φ s₁) holds, and for every s₀ there is a k with EisRegularAt V (flat V a φ s₁) s₀ k. These names are unopened.
- `siegelEisensteinSimplePole`. Its type is UnusedSlot72, which the dossier shows to be an abbreviation for True. This field therefore asserts nothing, whatever its name says.
- `schurOrthogonalitySquareIntegrable`. For a locally compact Hausdorff group G with a regular right-invariant Haar measure μ and a norm-preserving, strongly continuous homomorphism π into bounded operators on a complex Hilbert space H whose only closed invariant subspaces are zero and H, if one coefficient g ↦ ⟨w₀, π g v₀⟩ with nonzero v₀, w₀ is square-integrable then all coefficients are. Moreover there is a real d > 0 such that the integral of ⟨w, π g v⟩ times the conjugate of ⟨w', π g v'⟩ equals ⟨v', v⟩⟨w, w'⟩/d for all v, w, v', w'.
- `litN`. A sub-bundle NonEndoscopicHypothesesAlt with five fields. They are loc (a bundle of 19 local statements), aut (a bundle of 16 global statements), coh (the bundle LitCoh of 12 statements), join (the five-fold conjunction JoinOut of unopened propositions) and fe (HeckeTateFunctionalEquation, which gives functions Λ and Λ' with IsCompletedL and Λ s = archEps n * finEps χ a s * Λ' (1 − s)).
- `toHypothesesX`. A sub-bundle GeometricGaloisRepCompatibility with twelve fields. Ten repeat statements already listed above (weil, ds, ana, dsc, trc, dm, flath, sw, dbl, udbl), and the other two are HeckeLPartialContinuation (entire nonvanishing continuations on real part ≥ 1 for heckeL T χ and for (s − 1) times zetaOff T s) and HtCard, defined as the unopened PhtCmp.
- `nLink`. A sub-bundle Hypotheses₂ with seven fields, namely FontaineBcris (seven unopened conditions on every C of type Core l), GlobalArtinReciprocity again, BlochKatoLocal (three unopened conditions), the three statements LocalTateDualityK, LocalEulerCharK and LocalFinitenessK, and BhattScholzeIntegral. The K-statements concern finite modules M over the integers mod l^r with a continuous action of GK l K and say that H0, H1, H2 are finite with Hn trivial for n ≥ 3, that card H1 = card H0 * card H2 * (card M)^(dimension of K over the l-adic numbers), and that certain cup-product maps are bijective.
- `depthZeroSupport'`. The proposition DepthZeroSupport. For π in Irr k n with IsCuspSupport data σ, if π has a nonzero vector fixed by KOne k (Fin n) then every σ a has a nonzero vector fixed by KOne k (Fin (d a)).
- `localFiniteness`. For every number field F with algebraic closure Ω, prime l, exponent r, finite discrete module M over the integers mod l^r, valuation subring A of Ω, representation rho of Dec A on M and prime v of F, the unopened condition LocalFinitenessAt A rho v holds.
- `localTateDuality`. The same quantifiers as localFiniteness, with the unopened conclusion LocalTateDualityAt A rho v.
- `localEulerChar`. The same quantifiers as localFiniteness, with the unopened conclusion LocalEulerCharAt A rho v.

The reading does not open the names `GlobalTheory.GLq.Green`, `GlobalTheory.TripleGal.CharAbove`, `GlobalTheory.NT.RayField`, `ResidueKilled.DM`, `DiscreteSeriesUpqExists`, `AdmissibleCoefficientsAnalytic`, `LeviSubmoduleDense`, `JacquetShalikaRigidity`, `JacquetShalikaBound`, `HarishChandraModulesOn`, `KFiniteAnalyticUJ`, `SiegelWeilAt`, `LocalFinitenessAt`, `LocalTateDualityAt`, `LocalEulerCharAt`, `GlobalTheory.SmGL.JacquetOfInducedFiltration`, `PhtCmp`, `UpperTheory.GalS.IsGalUAlt`, `IsGlobalArtin`, `IsLAdicOf`, `IsAlgPos`, `HChar`, `Ideles`, `Gab`, `G`, `Qbar`, `CuspSub`, `CG.mk`, `IsRegAlg`, `IsCsd`, `IsPolarized`, `IsLocComp`, `GKCoh.IsCohomological`, `IsCMField`, `IsCMExt`, `IsHermND`, `IsAutRepU`, `IsBaseChangeU`, `UA`, `Sm`, `SmIrr`, `D7`, `HSp`, `GA`, `AE`, `AF`, `WO`, `dblSp`, `wittIdx`, `IsInfFam`, `IsExpFam`, `IsAutFun`, `IsSmoothInf`, `IsUnifModerate`, `IsCuspFun`, `CuspDecay.IsRapidDecay`, `IsTraceClass`, `RcuspOp`, `CcGA`, `IsFrameFam`, `IsWeilDatumO`, `IsThetaFunO`, `IsFockVec`, `IsWeilSch`, `IsHeckeChar`, `ResEta`, `IsStdChar`, `IsMaj`, `HasIwasawa`, `IsCartanInv`, `IsCovolOne`, `thetaKO`, `swSection`, `CosetConv`, `cosetSum`, `Eis.EisValueAt`, `EisContinues`, `EisRegularAt`, `HolValueAt`, `degPS`, `flat`, `absThetaInt`, `LocPrime`, `LocAinf`, `LocTied`, `LocBridge`, `IsAinf`, `IsStd`, `IsCrys`, `IsDR`, `IsPst`, `FCrys`, `FHom`, `Realises`, `Pst.Induces`, `wdAt`, `UpperTheory.Zero.LLC.IsRecT`, `NcW`, `Ab`, `Dec`, `IsPlaceOver`, `Ine`, `IsFrob`, `normV`, `Irr`, `IrrGL`, `IrrRep`, `IrrCl`, `Segment`, `GrothGL`, `IsSegmentClass`, `IsProductIso`, `IsCuspSupport`, `KOne`, `KO`, `unipRad`, `Jacquet`, `ind₂`, `extTensor`, `parInd`, `jac`, `contra`, `HasFiniteLength`, `IsAdmissible`, `IsGeneric`, `GenericUnitary.IsComplementaryProduct`, `LFactors`, `IsCosocle`, `HasSatake`, `IsZonal`, `sphSection`, `lFactor`, `invNormFactor`, `GrpData`, `DSRep`, `IsParam`, `HasTypes`, `HasParam`, `UnitEquiv`, `CDHaar`, `IsDS`, `IsURepOn`, `IsIrredOn`, `IsSqIntOn`, `HasInfChar`, `IsKTypeOf`, `UJset`, `IsSmoothModRep`, `IsGKMap`, `IsKFin`, `IsSmoothGMap`, `SmoothVec`, `sobNorm`, `CcMat`, `conv`, `IsIrrUnitary`, `Flath.IsUnramFactorisation`, `IsPlacesIdem`, `SUSupp`, `SUAdelic`, `SURat`, `Gn`, `IsRegularChar`, `IsCusp`, `IsGoodCMCurve`, `HasMinimalDiscriminant`, `weberSet`, `IsAbelianGalois`, `IsRay`, `idealsPrimeTo`, `primeElt`, `IsAutForm`, `AutFin.coeffSpan`, `CuspidalSpectrumGL`, `BaseChangeIsobaricTransfer`, `GelfandKazhdanDual`, `UpperTheory.GalS.PairUAlt`, `UpperTheory.One.M.Row`, `ClozelPurity`, `AlgebraicCharacterWD`, `PoitouTateNormalised`, `GlobalFiniteness`, `GlobalEulerChar`, `UnramifiedOrthogonality`, `GreenbergWiles`, `GeometricLemma`, `TotallyDisjointProductIrreducible`, `MoyPrasadJacquetIso`, `TemperedProductOfSquareIntegrable`, `EssSquareIntegrableSegments`, `SquareIntegrableSegment`, `GenericUnlinkedGL`, `LanglandsMultisegments`, `LanglandsExhaustionGL`, `UpperTheory.Zero.LLC.RecTExists`, `LocalConverseGL`, `DepthZeroInduction`, `BrauerDegreeZero`, `ChevalleyUnits`, `ToricDenominator`, `Transport`, `TwistedTransport`, `ZetaDenominators`, `GlobalTheory.SqTop.Refl`, `Core`, `BlochKato.DimFormula`, `BlochKato.RationalDuality`, `BlochKato.IntegralDuality`, `IsCMType`, `IsCompletedL`, `archEps`, `finEps`, `heckeL`, `zetaOff`, `ContAction`, `H0`, `H1`, `H2`, `Hn`, `cycK`, `cupH0H2TwistedDual`, `cupH1H1TwistedDual` and `cup20`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest a list of published theorems taken as assumptions for an argument about unitary groups and theta lifts, covering results attributed by name to Clozel, Green, Chebotarev, Bhatt and Scholze, Bernstein and Zelevinsky, Harish-Chandra, Casselman and Wallach, Jacquet and Shalika, Flath, Dixmier and Malliavin, the Siegel-Weil formula, the doubling method, class field theory and local Galois cohomology. This is a suggestion from the names only, and the name siegelEisensteinSimplePole in particular is misleading because its content is True.

The reader's confidence is medium. The structure and the outer logical shape of all 60 fields are visible, but most of the statements rest on predicates and objects whose bodies the dossier does not reach, and five fields are bare names with no body.

The check found no error in this reading.

The check found 5 errors in the second reading, which the text above does not use.

### `LinkedAt`

The full name is `GlobalTheory.Fc.RL.LinkedAt`, a def in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Row Good. 4,236 or more project definitions lie below it, and the reader saw 84 of them. The reader describes it as a proposition-valued function of two arguments (a predicate on a parameter record and a test relation).

LinkedAt takes a parameter record p and a relation r on pairs (slot, linkage) and returns a proposition. A slot is a predicate on tuples (K, X, f, T, c), where K is a context, X a record of stages, f a frame, T twisting data and c a core record over them. Unfolding the one visible layer Lg1, the proposition says that there exists a slot R such that both of the following hold. First, the condition the code calls LargeBaseCondition holds for the base predicate KPx, the slot IsBuiltE p.s and R. Second, r holds of the pointwise conjunction of the slot IsGoodE p.s with R, paired with the linkage BundleLinkage p.

- `hL (implicit argument)`. This is a proof of the proposition RecTExists, which says that for every number field E, algebraic closure Ω, valuation subring A of Ω, finite place w of E and proof h that A lies over w, there exists a map rc satisfying a condition that the code calls IsRecT. It enters only as the index of the type of p.
- `p`. This is a record of the type Parameters hL, whose four fields are R of type RPosition, N of type NormChoiceExtension hL, S of type SExt and Γ of type GeoP. The body uses it only through p.s, an object of the type Slots obtained by a projection the dossier does not show, and through BundleLinkage p.
- `r`. This is an arbitrary relation that takes a slot and a linkage for BundleCondition and returns a proposition. A linkage here is a predicate on a context K, a point β of type BPt K, a real number c and a bundle b of type BundleCondition β.D β.O c.
- `Lg1 (the outer shape)`. Lg1 KP Q Q' r' is by definition the statement that there exists a slot R with LargeBaseCondition KP Q R and r' (sAnd Q' R). Here sAnd Q' R is the slot that holds at (K, X, f, T, c) exactly when both Q' and R hold there.
- `KPx (first argument of Lg1)`. This is the predicate on a base B and a frame f that is the conjunction of two statements. The first says that there exists δ of type FieldDat B.toPre with a condition that the code calls B.KsExact δ f, and the second is PrePin B.toPre, which says that the map iX' sends each frame vector of the space X' to the frame vector of the space X at index R.m having the same index number.
- `IsBuiltE p.s (second argument of Lg1, the slot Q)`. This is the slot positionOf (BuiltE p.s). It holds at (K, X, f, T, c) when there exist w of type ColW X.B f T, Z of type w.Lt and a core c' over the stages w.st Z such that there exists b of the type that the code calls Built p.s K w Z c' satisfying a condition that the code calls EntC b.ker, and such that the dependent triple made of X.C, the later stages of X and c equals the triple (w.C, Z, c').
- `LargeBaseCondition KPx (IsBuiltE p.s) R (first conjunct)`. This applies an operator that the code calls EvLg to the predicate on (K, B, f, T) which says that if KPx B f holds then, for all stage data C, W, V, S, N, G over B and every core c over the resulting stages, IsBuiltE p.s at that tuple implies R at that tuple. The dossier does not show the body of EvLg.
- `IsGoodE p.s (third argument of Lg1, the slot Q')`. This is the slot positionOf (GoodE p.s), built in the same way as IsBuiltE p.s. Its inner condition GoodE is the conjunction of BuiltE p.s with a condition that the code calls GoodO (w.D Z) c.O.nch c.O.xd.
- `fun S => r S (BundleLinkage p) (fourth argument of Lg1, giving the second conjunct)`. This feeds r the slot S together with the fixed linkage BundleLinkage p, so the second conjunct reads r (sAnd (IsGoodE p.s) R) (BundleLinkage p). BundleLinkage p is the linkage that holds at (K, β, c, b) when there exist q of type WPt p.s K and a bundle b' of type BundleCondition (q.w.D q.Z) q.O c such that the record type BundleWitness q b' is nonempty and the dependent triple (β.D, β.O, b) equals (q.w.D q.Z, q.O, b').
- `Q and Lk (variables in scope)`. The surrounding section declares a slot Q and a linkage Lk, but neither appears in the signature or the body of LinkedAt. They play no role in what the definition states.

The reading does not open the names `EvLg`, `p.s (the projection from Parameters to Slots)`, `Built`, `EntC`, `GoodO`, `ColW`, `WPt`, `KsExact`, `Pre`, `IsRecT`, `LawsT`, `TC.Later`, `Cols`, `RowsRest`, `DivStage`, `SStage`, `NStage`, `GJStage`, `RowsT`, `BaseLevelRowSide`, `NormChoiceCore`, `SX`, `ColT`, `SPosition`, `NCondition`, `OComponent₂`, `TwistedBundle`, `RecordCompatibleExtended`, `Extra`, `TiedDataSKAlt`, `IndefiniteRealisation`, `Scale`, `Obj2`, `LedPart` and `Lay`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. As a suggestion only, the names hint that EvLg means "eventually, for all sufficiently large scale contexts", so that the first conjunct would say that built positions eventually lie in R over good bases. On the same footing, LinkedAt would say that r holds at the good built positions cut down by such an R, together with the linkage of bundles that have a witness at a weighted point of p.

The reader's confidence is medium. The logical shape through Lg1, sAnd, positionOf, linkOf and KPx is fully visible, but the operator EvLg, the projection p.s and the inner conditions Built, EntC, GoodO and the content of BundleWitness rest on names the dossier does not open.

The check found no error in this reading.

### `parametersOfDependence`

The full name is `GlobalTheory.Mem.Top.Bl.parametersOfDependence`, a def in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Prm1. 3,453 or more project definitions lie below it, and the reader saw 87 of them. The reader describes it as a function that builds a record.

It is a function that takes a proof hL of the proposition that the code calls RecTExists and a real number cDep, and returns a record of the type that the code calls Parameters hL. That record type has four fields named R, N, S and Γ. The function fills R with the fixed choice RX, fills N with extensionWithList hL cDep, fills S with SExt.none and fills Γ with geoCl anyGeometry. The real number cDep enters only through the field N, where it appears as the constant CF inside one existence condition called ListPin.

- `hL`. This argument is a proof of the proposition RecTExists. The text shows that proposition to say that for every number field E, every algebraic closure Ω of E, every valuation subring A of Ω and every height one prime w of the ring of integers of E with a proof h of the condition that the code calls IsPlaceOver A w, there exists a map rc that satisfies the condition that the code calls IsRecT h rc.
- `cDep`. This argument is a real number. It is passed unchanged to extensionWithList, where it becomes the middle entry of the triple ⟨1, cDep, b⟩ that indexes an object of the type that the code calls GridData.
- `result type Parameters hL`. The result is a record with four fields, R of the type RPosition, N of the type NormChoiceExtension hL, S of the type SExt and Γ of the type GeoP. The first three types are families that assign a type to each long tuple of project data (K, B, f, T, w, Z, Wt, p0 and further entries), and GeoP is a family that assigns a true or false statement to each triple made of a D7, a Core of it and a DivX of it.
- `parametersOfExtension`. This helper takes N, S and Γ and returns the record ⟨RX, N, S, Γ⟩. So the field R is always RX, which sends each tuple of data ending in an object t of the type RowsT to the record type that the code calls RXs t.
- `field N, extensionWithList hL cDep`. For each tuple of data this is the product of two types. The first is extensionWithLaw applied to the same data, which is itself the product of defaultExtension (an object of the type that the code calls RealExpansionExtraData) with a proof of BkLaw (w.D Z), the implication from the condition called RationalMapValues to the condition called BuRational. The second is a proof of ListPin for the data and cDep, which says that there exists a GridData G with index ⟨1, cDep, K.s.b⟩ satisfying both the condition called FieldHas G (embLL0 D) and the condition called IsLamTieFull D.ntw (lamOf G).
- `field S, SExt.none`. This is the constant family that sends every tuple of eleven arguments to PUnit, the type with exactly one element. It therefore carries no data.
- `field Γ, geoCl anyGeometry`. The predicate anyGeometry is true on every triple. The predicate geoCl Γ is the inductively generated closure GeoCl Γ, which holds wherever Γ holds and is carried from (D, J, X) to (setDiv D N h, coreS N h J, divTr N h X) by a step rule. Since the base rule already applies to every triple, the text shows this closure of the always true predicate to hold on every triple too.

The reading does not open the names `IsRecT`, `LawsT`, `IsPlaceOver`, `RXs`, `RowsT`, `NormChoiceCore`, `RealExpansionExtraData`, `BkLaw`, `WeightDegreeSizes.RationalMapValues`, `D7.BuRational`, `GridData`, `FieldHas`, `embLL0`, `IsLamTieFull`, `lamOf`, `LevCh`, `D7`, `Formalism.L2.Pj.Core`, `DivX`, `setDiv`, `coreS`, `divTr`, `Ctx`, `ColW`, `SX`, `ColT`, `NChoice`, `NchT`, `ThData` and `BaseLevelRowSide`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that hL is an assumed existence of a local Langlands reciprocity map, and that the record collects the adjustable parameters of a large membership statement, with cDep a constant of dependence that fixes the size of a grid or list of characters. This is a suggestion from the names and module paths only.

The reader's confidence is medium. The top definition and its four field values are fully visible down to two or three levels, but the types they range over and the conditions inside ListPin, BkLaw and RXs rest on many names whose bodies the dossier did not show.

The check found no error in this reading.

### `SlotNormCondition`

The full name is `GlobalTheory.Fc.R1.SlotNormCondition`, a def in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Counts Irreducibility Constants. 3,404 or more project definitions lie below it, and the reader saw 87 of them. The reader describes it as a proposition (a property of three arguments Q, Lk and N), defined by specialising a general existence statement that the code calls Row.

Given a slot predicate Q, a link predicate Lk on bundles of the type BundleCondition, and a property N of family classes, the definition is the proposition Row Q Lk H, where H sends a family class 𝒜 and a selection to the statement N (D3 3 𝒜) and ignores the selection. Unfolded one step, it states that there exists a map E, from parameter records of type Par to predicates on bundles, such that RowE Q Lk E holds, and such that for every family class 𝒜 and every raw selection σ for 𝒜, if IsSel Q Lk E 𝒜 σ holds then N holds of the family class D3 3 𝒜. Here D3 3 𝒜 is the class 𝒜 strengthened by a fixed list of further conditions, with the real constant 3 placed in the slot C0, and with the bound Fm.CYL ≤ 9 among the added conditions. A family class is a predicate on parameter families Fm of type FamP eps, for every real eps.

- `Q : V4.Slot`. The first argument is a predicate that takes a context K of type Ctx, a record X of type Stages, a frame f of type Fr X.B.toPre, a record T of type TwDat X.B and an object of the type V4.Core K X f T, and returns a proposition. The definition only passes it on to Row.
- `Lk : LkT BundleCondition`. The second argument is a predicate that takes a context K, a point β of type BPt K, a real number c and a bundle of type BundleCondition β.D β.O c, and returns a proposition. BundleCondition D O c is a record with seven fields R, S, P, pin, DH, C and B, where DH is a pair of natural numbers p with D.s.Del = p.1 as a rational and O.L.etaSz = D.R.m times p.2 as a real.
- `N : FamClass → Prop`. The third argument is a property of family classes. A family class is a predicate that assigns a proposition to every parameter family Fm of type FamP eps, for every real eps.
- `Row Q Lk (…)`. The body applies Row with the bundle type taken to be BundleCondition. Row Q Lk H says that there exists E, a map from Par to predicates on bundles over all D, O and c, such that RowE Q Lk E holds and such that for all 𝒜 and all raw selections σ, IsSel Q Lk E 𝒜 σ implies H 𝒜 σ. A raw selection for 𝒜 gives, for each family Fm in 𝒜, each real x above Fm.x1 and each index i in Fm.Ix x, a bundle over Fm.D x i, the object that the code calls objAt Fm x hx i, and the constant Fm.Csz.
- `RowE Q Lk E (inside Row)`. This is the condition that the code calls EvP applied to the predicate on pairs κ, K which says that for every point β of BPt K with β.Is Q, every real c and every bundle b over β.D, β.O, c, if Lk K β c b holds then E κ β.D β.O c b holds. The wrapper EvP and the condition β.Is Q have no visible body.
- `IsSel Q Lk E 𝒜 σ (inside Row)`. This says that for every real eps and every family Fm with 𝒜 Fm there exists a parameter record κ of type Par, with seven fields eps, C, cD, ch, C5, c6 and Cb, such that three things hold. They are the condition that the code calls Link κ Fm, the condition that the code calls DQ.cls7 with the trivially true predicate at Fm, and, for every x above Fm.x1 and every index i, both the condition that the code calls Built Q Lk κ at the selected bundle σ Fm hc x hx i and E κ at that same bundle.
- `fun 𝒜 _ => N (D3 3 𝒜)`. This is the conclusion H handed to Row. It ignores the selection and asserts N of the class D3 3 𝒜, which is Des (WithChN 𝒜) 3. WithChN 𝒜 holds of Fm when 𝒜 Fm, DGamDvdF Fm, TameDistinctF Fm, BoxesF Fm, QDRowsF Fm and Fm.CYL ≤ 9 all hold. Des of that class with constant 3 adds DGamSmooth Fm, TwGood Fm, the existence of a real CH with ChosenE Fm 3 CH, TuSize Fm and DGamSize Fm.

The reading does not open the names `EvP`, `BPt.Is`, `BPt.D`, `BPt.O`, `Link`, `DQ.cls7`, `Built`, `objAt`, `FamP.CYL`, `Chosen`, `TwGoodE`, `twE`, `FactDGam`, `minkM`, `TameDistinct`, `Boxes_at`, `GlobalTheoryTheory.BoxE`, `QDRows_at`, `SizeData₂.TuGe`, `Ranks`, `SizeData₂`, `FC`, `Scale`, `Base`, `Obj2`, `Lay`, `LedPart`, `TiedDataSKAlt`, `STies`, `IndefiniteRealisation`, `ColRec3`, `FamIn3` and `the field types of BundleCondition (RecTAlt, STiesRAlt, RowSideFamily, RowSideDeterminedAlt, SquareIntegrableColumns, RealTBAlt) below their field lists`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. As a suggestion only, the names hint that this is a "norm" condition attached to a "slot" of a construction, which would say that eventually in the parameters (EvP), every bundle built at a point in slot Q and linked by Lk satisfies some property E, and any family class whose members can all be served by such bundles has its strengthened "design" class D3 3 𝒜 satisfying N. The module names mention theta correspondence and abelian varieties, but the text shown does not confirm what any of that means here.

The reader's confidence is medium. The logical shape of the definition, Row, IsSel, RowE, D3, Des and WithChN are all visible with their constants 3 and 9, but the key conditions EvP, β.Is, Link, DQ.cls7 and Built, and most of the underlying data types, have no visible bodies.

The check found no error in this reading.

### `BoundAtTwoThreeFamilyFonAlt`

The full name is `GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt`, a def in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Bound At Two Three Family Fon. 1,235 or more project definitions lie below it, and the reader saw 63 of them. The reader describes it as a proposition about a family record Fm of the type that the code calls FamP eps, where eps is a real number.

It is a proposition that depends on a real number eps and on a record Fm of the type FamP eps. It states that there exist real numbers C and x0 such that the following holds for every real x with x ≥ x0, every proof hx that Fm.x1 < x, every index i in Fm.Ix x, every HW, every F, every piece of comparison data built over F, every record X of type HubData for the datum Fm.D x i, and every real number C₂. If the condition SetupAlt holds for Fm.L x i, the component nch of Fm.ex x hx i, HW, X and C₂, then the condition BoundAtTwoThree holds for Fm.L x i, the component ρ of X, and the constant C. The constants C and x0 are chosen once, before x, i and all the other data, so the same C serves the whole family. The objects F and the comparison data are quantified over, yet they appear neither in the hypothesis SetupAlt nor in the conclusion.

- `eps`. An implicit real number that only serves as the parameter of the type FamP eps of the family.
- `Fm`. A record of the structure FamP eps, which extends an unshown structure FamCore eps. The definition uses its components x1, Ix, D and L, which come from the unshown FamCore, and its field ex, which for each x with x1 < x and each i in Ix x gives a record of the type called Extra.
- `∃ C x0 : ℝ`. Two real numbers are asserted to exist, placed outside all the other quantifiers. C is the constant handed to the conclusion and x0 is a threshold for x.
- `∀ x ≥ x0`. The statement is required for every real number x that is at least x0.
- `hx : Fm.x1 < x`. A proof that x exceeds the number Fm.x1 of the family. It is needed because the field ex of Fm is only defined for such x.
- `i : Fm.Ix x`. An index taken from the index type Fm.Ix x that the family attaches to x. It selects the datum Fm.D x i, which the header's variable declaration suggests is of type D7, and the object Fm.L x i.
- `HW : HWOf (Fm.D x i).loc`. By the shown body of HWOf this is a choice, for every prime number l, of a record of the structure LocHW at l over the l-th component of (Fm.D x i).loc. LocHW has fields W, W_s and W_proj, whose types rest on the unshown names LocWach, Good and FinExt.
- `F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW`. By the shown body of FonOf this is a choice, for every prime l, of a record of the structure LocFon at l. That record has one field E, which for each K, s, LL and proof of Good K s LL gives an object of the type that the code calls EtSit.
- `unnamed argument of type CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F`. By the shown body of CmpOf this is a choice, for every prime l, of a record of the structure LocCmpT at l built over F. That record has one field C, which gives objects of the type that the code calls CmpSit. The argument has no name and is not used afterwards.
- `X : KillingConditions.HubData (Fm.D x i)`. A record of the structure HubData for the datum Fm.D x i, with fields r, ρ, len0, errorBoundHub, dc, lenRow, e', cB, eS, c0, band, exc, eta and I. The whole record goes into the hypothesis and only its field ρ, of the type called RhoFam, goes into the conclusion.
- `C₂ : ℝ`. A real number, universally quantified, which appears only in the hypothesis SetupAlt, where it enters through the expression rowC C₂.
- `hypothesis SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂`. A proposition given as a record of eight conditions named facts, canon, par, par67, big, split, kill and sha. Two of them are readable, namely big, which says 8 ≤ L.sc.L, and split, which says 60 ≤ D.host.splitBound, where splitBound is a natural number field of the host record. The other six are conditions that the code calls NormChoiceFacts, HubX.Canon, AdmPar, ParametersPolynomiallyBounded, KillAt (applied to X.ρ) and ShaFinOdd.
- `conclusion BoundAtTwoThree (Fm.L x i) X.ρ C`. By its shown body, with D standing for Fm.D x i and L for Fm.L x i, this says the following. For every i' for which the condition called TwLoc D i' holds, and for which either D.nd.l i' = 2 or both D.nd.l i' = 3 and D.nd.l i' is not in D.host.small, every π in the set D.nd.Zgood i' satisfies the condition that the code calls Bd, applied to ρ, i', π and the quantity midF L C.

The reading does not open the names `FamCore (source of Fm.x1, Fm.Ix, Fm.D, Fm.L)`, `D7.loc`, `D7.locA`, `D7.nd`, `D.nd.l`, `D.nd.Zgood`, `D.host.small`, `SizeData₂`, `L.sc.L`, `NChoice`, `GlobalTheory.NFacts.NormChoiceFacts`, `GlobalTheory.HubX.Canon`, `rowC`, `AdmissibleParameterJ.AdmPar`, `EmbeddingTypeJumps.ParametersPolynomiallyBounded`, `KillingConditions.KillAt`, `TwistedPlaces.ShaFinOdd`, `TwistedPlaces.TwLoc`, `Bd`, `midF`, `FamilyRepresentationConstants.RhoFam`, `FamilyRepresentationConstants.RFam`, `LocPrime`, `LocWach`, `EtSit`, `CmpSit`, `Good`, `FinExt` and `Extra (most of its field types)`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. As a suggestion only, the names point to a uniform bound, with one constant C for a whole family of arithmetic data indexed by a growing real parameter x, on some quantity attached to local places of residue characteristic 2 and 3. The words Fon and Alt suggest a variant of an earlier family statement that additionally assumes local p-adic Hodge theoretic data (Wach module style data HW, data F perhaps named after Fontaine, and a comparison) under an alternative set of setup hypotheses.

The reader's confidence is medium. The quantifier structure, the two numerical conditions 8 ≤ L.sc.L and 60 ≤ D.host.splitBound, and the case split at 2 and 3 are fully visible, but the family core FamCore, the bound Bd with midF, and six of the eight setup conditions have no body in the dossier.

The check found no error in this reading.

### `KPx`

The full name is `GlobalTheory.Mem.Top.Bl.KPx`, a def in the module Development › Abelian Variety Theory › Definitions › Automorphic Membership › Position Of Intro. 71 project definitions lie below it, and the reader saw 71 of them. The reader describes it as a predicate (a proposition-valued function) on pairs made of a record B of type Base and a record f of type Fr B.toPre.

KPx is an element of the type BaseP, which the dossier shows to be the type of functions that take a record B of type Base and a record f of type Fr B.toPre and return a proposition. For given B and f, KPx B f is the conjunction of two statements. The first statement says that there exists a record δ of type FieldDat B.toPre such that a condition that the code calls B.KsExact holds of δ and f. The second statement is PrePin B.toPre, which says that the linear map iX' of the underlying Pre record sends each basis vector of the space X' to the basis vector with the same index in the space X at index R.m. The second statement does not depend on f.

- `B`. B is a record of type Base, which extends the record type Pre. On top of the Pre data it adds a number field LL that is Galois over ℚ with a star operation and an embedding embLL into ℂ, a ring map embE from the host field E into LL, two intermediate fields LL0 and Ks with Ks inside LL0, and conditions asking for certain roots of unity in Ks, LL0 and LL and for ideals of E to become principal in Ks.
- `f`. f is a record of type Fr B.toPre, which unfolds to Chr.HFrame B.host with exponent function sending j and g to the entry e j of B.hc g. Such a record holds an object P of type PiBar (a choice of a prime of the field K above each of the two primes g 0 and g 1), an object W of type Omg (an injective character of the units of the integers modulo g k for each k), characters mu0 j, eta, chiPsi, del and del' of type HChar of the host field E, and proofs of the conditions IsMu0, IsEtaT, IsChiPsi, and IsDelta at the primes pde and pde'.
- `first conjunct, ∃ δ : Fld.FieldDat B.toPre, B.KsExact δ f`. This says that some record δ of type FieldDat for the Pre part of B exists for which the condition that the code calls B.KsExact holds of δ and f. The dossier shows no body for KsExact, so what the condition demands is not visible.
- `δ`. δ is a record of type FieldDat P with P equal to B.toPre. It holds a subfield ray of ℂ with a proof of IsRayFieldIn for the embedding φ₀ and the ideal of the integers of E generated by the natural number g 0 * g 1 * pde * pde', a subfield jField of ℂ, a Weierstrass curve over jField with a proof of IsGoodCMCurve for the number d, and a ClassBasis of E, which is a finite family of invertible fractional ideals c i and units γ i whose classes generate the class group independently and satisfy c i raised to the order of its class equals the principal ideal of γ i.
- `second conjunct, PrePin B.toPre`. With the star structure that the code calls host.cmStar in force, this says that for every index a below the rank of the space sp.X' and every index b below the rank of the space sp.X R.m, if a and b are equal as natural numbers then the linear map sp.iX' sends the a-th vector of the stored basis (frame) of X' to the b-th vector of the stored basis of X R.m. The symbol ∀ means for all, and Fin n is the set of natural numbers below n.

The reading does not open the names `GlobalTheory.Mem.Base.KsExact (written B.KsExact)`, `Host.cmStar`, `IsAbelianGalois`, `PeriodPair`, `Pre.restRowsFiniteGroupCard`, `Pre.ramOrder`, `Ranks.Psi`, `Ranks.sigW`, `the fields of Host, Spaces, HostDer and HostRaw that lie past the cuts` and `the HChar conditions IsUnitary, UnrAt, TameAt, TrivOn, HasInf, HasInfQ, ResEta, OrderDvd, loc and locK`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. As a suggestion only, the name KsExact hints that the field Ks of B is required to be exactly some field built from the data δ, such as a compositum involving the ray field and the field of the CM curve, in a way tied to the characters in f. The name PrePin hints at pinning the frame of X' to the initial segment of the frame of the top space X.

The reader's confidence is medium. The overall shape, the types of B, f and δ, and the whole second conjunct are visible, but the central condition KsExact in the first conjunct has no body in the dossier.

The check found no error in this reading.

### `BundleCondition`

The full name is `GlobalTheory.Fc.BundleCondition`, a structure in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Column Choice With Ties. 3,045 or more project definitions lie below it, and the reader saw 57 of them. The reader describes it as a record type (a structure with seven fields, living in the universe Type 1) that depends on three parameters.

For a base datum D of type D7, an object O of type Obj D and a real number c, BundleCondition D O c is the type of records that bundle seven components built over the component O.ex of O. Five components are data, namely a record R, a record S that depends on R, a record P, a record C that depends on R.T and P, and a record B that depends on R, P, C, S and a scale function. One component, pin, is a proof of a proposition about R.T and P. One component, DH, is a pair of natural numbers together with a proof of two equations, the first saying that D.s.Del equals the first number read as a rational, and the second saying that O.L.etaSz equals the real number D.R.m times the second number. The real number c enters only through B, where the scale function zsc P DH.1.1 DH.1.2 c is formed from P, the two natural numbers of DH and c.

- `D`. This argument is a record of the type that the code calls D7, a large structure whose first fields are a rank record R, a host record, spaces, a positive volume function and a rows record called what₂. The dossier shows only the first 3,000 of the 9,862 characters of D7.
- `O`. This argument is a record of type Obj D, which the dossier shows to have eight fields L, gatT, Gx, Gy, K, X, cX and ex. The last field ex has the type Extra D L gatT Gx Gy K X cX, and it is O.ex that most of the fields below are built over.
- `c`. This argument is a real number. It is used only in the last field, where it is passed to the function zsc.
- `R`. This field is a record of type RecTAlt O.ex. The dossier shows that such a record has five fields, namely T of the type called TiedDataSKAlt O.ex, pin of the type called RowPinMinAlt T, joints of the type called JointsSAlt, host of the type called HostDatumSelfDual, and weq of the type called WeilCompatibleEquivariance, and none of these five types is opened.
- `S`. This field is a record of type STiesRAlt R. The dossier shows that it extends a record called STies D and adds, for every word u, a transport tr u with conditions called ColDictInto, ColDictBij and LevelMatch, an equation colPin that identifies a column dictionary value with D.s_Cu u x, an equation inst, an object G of the type called GoodOp, a condition rowTie and a condition called LocTied D.
- `P`. This field is a record of type RowSideFamily O.ex. The dossier shows that it holds a finite group Gp, three further types Pl0, I0 and T, an object A3 of the type called FamIn3, two subgroups P0 and Ps of Gp with homomorphisms ψ0 and ψs into the units of the field D.what₂.LL, an object Zs of the type called DefSub, and further objects S0, S1, Dc, Sp, C, NuC, I, JA, JM and tied whose types are not opened.
- `pin`. This field is a proof of the proposition RowSideDeterminedAlt R.T P. The dossier shows that proposition to be a conjunction of six named conditions, lowerMap, lowerMapTw, buDef, ambS, faces and gamDvd. The condition faces says that there exist families Dcf and Spf indexed by all Zs whose values at P.Zs are P.Dc and P.Sp, and gamDvd says that the cardinalities of certain finite sets Gam c divide the natural number (D.mem D.u₀).C.DGam.
- `DH`. This field is a pair p of natural numbers together with a proof that D.s.Del equals p.1 read as a rational number and that O.L.etaSz equals the real number D.R.m times p.2 read as a real number. Here D.R.m is the field m of the rank record, which the dossier shows to be an even natural number that is at least 2, while D.s and O.L.etaSz are not opened.
- `C`. This field is a record of type SquareIntegrableColumns R.T P. The dossier shows that it holds an object X of the type called Fields, a family e of ring homomorphisms into D.what₂.LL, an object c of the type called ColRec3, a family Sp, conditions called ColTie3 and ColumnRecordCompatible, an infinite place v0 of D.what₂.LL, a finite set TU, and equations that identify P.A3, P.Gp, P.Pl0, P.I0 and P.T with objects built from c and X.
- `B`. This field is a record of type RealTBAlt R P C.c.face C.Sp (zsc P DH.1.1 DH.1.2 c) S, so it takes the two families from C, the record S and a scale function. The dossier shows that zsc sends each Zs to the object z given by ZscOfNum3 applied to P.A3, P.P0, P.ψ0, ofRecord D O.L Del h0, an identity bijection, O.L.Nc and Zs, and then replaces the component l6m j by z.l6m j minus c times z.l6u and sets the component l6u to 0. The record RealTBAlt itself has fields T, alg, Q, κ, v₀, fw, bar, O, pins, rhoGeo, equivAll, cTie and phase, whose types (CoreJ, IndefiniteRealisation, FWTie, BarTie, OMDat, OMPins, RhoGeo, EquivAll, CTie, PhaseTie) are not opened.

The reading does not open the names `D.s`, `D.s.Del`, `D.s_Cu`, `SizeData₂`, `O.L.etaSz`, `O.L.Nc`, `GatTies`, `G.Inst`, `G.LatInst`, `G.Consts`, `TiedDataSKAlt`, `RowPinMinAlt`, `JointsSAlt`, `HostDatumSelfDual`, `WeilCompatibleEquivariance`, `STies`, `ColDict.Transport`, `ColDictInto`, `ColDictBij`, `LevelMatch`, `GoodOp`, `RowDictTie`, `LocCP.LocTied`, `FamIn3`, `DefSub`, `IndefData`, `DefCols`, `SPer`, `ColData`, `DivisionCompatibilityDataThreeSided`, `AmbIds`, `MjHIds`, `BaseDivisionAmbientCompatibilityFamily`, `LowerMapTieS`, `LowerMapTieTwAlt`, `BuDefQ`, `AmbTie`, `Col.Fields`, `ColRec3`, `ColTie3`, `ColumnRecordCompatible`, `colIn3`, `IndefScale`, `ZscOfNum3`, `DIV.ofRecord`, `l6m`, `l6u`, `CoreJ`, `IndefiniteRealisation`, `WeightFamilies.Wt`, `FWTie`, `BarTie`, `OMDat`, `OMPins`, `RhoGeo`, `EquivAll`, `CTie`, `PhaseTie` and `phEff`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. As a suggestion only, the names point to a package of compatibility data for a theta correspondence construction, with row-side and column-side families, spectral ties, square-integrable columns and a real realisation of an indefinite form, where c shifts a scale parameter. The field D.s is probably a record of the visible type SData, whose field Del is a positive rational, so DH would say that this rational is a natural number and that a size parameter etaSz is m times a natural number, but the dossier does not show the field D.s itself.

The reader's confidence is medium. The dossier shows the full text of the structure, the field lists of all seven field types and the body of zsc, but almost every type inside those field lists, and the cut part of D7 containing D.s, remains unopened.

The check found no error in this reading.

The check found two errors in the second reading, which the text above does not use.

### `MIstar2`

The full name is `Formalism.IndefR.Cx.CxData.MIstar2`, a def in the module Formalism › Local To Global › Indefinite Real › Isometric Periods Of Unit Hypotheses. 13 project definitions lie below it, and the reader saw 13 of them. The reader describes it as a proposition (a true-or-false statement) that depends on a data record X, a map fc and two further maps eV and sEE.

MIstar2 is a proposition attached to a record X of the type CxData A, where A is a record of type DefAmb Bs over a number field K with a star operation. Besides X it takes a function fc from DefSub A to DefFace Bs, a family of K-linear maps eV and a conjugate-linear map sEE. It states that there exists an object d of the type that the code calls X.MIDat fc such that three conditions hold together, namely the condition that the code calls X.MIUnit2 d, the condition that the code calls X.MIid eV sEE d, and the condition that the code calls X.AuNZ d. The dossier shows no body for any of these four names, so the text only shows the shape of the statement, which is one existential quantifier over d followed by a conjunction of three conditions. No numbers or constants appear in it.

- `X`. X is a record of type CxData A. The dossier shows that such a record holds, among other fields, finite-dimensional complex inner product spaces FC t, EE, FLC j t and W j, maps jR and jL into them from the K-modules A.FR t and A.FL j t that are semilinear along the embedding of the place Bs.v0, complex linear maps Θ and θ', several families of subspaces, and real-valued and index-valued parameters.
- `fc`. fc is a function that sends each record of type DefSub A (a choice of K-submodules Z t of A.FR t and Zl j t of A.FL j t) to a record of type DefFace Bs. A DefFace holds two records Df0 and Df1 of type DefSide Bs, a record Dc of type DefCols Df1, a record Sp of type SPer Dc and a record Z of type IndefScale Bs.
- `eV`. eV gives, for every index t in the type Bs.Tup, a K-linear map from the space of n-tuples of elements of K into the K-module A.FR t. Here n is the natural number (fc X.zs).Df1.nV t, which is the field nV of the side Df1 of the face that fc assigns to X.zs, and X.zs is an object that the dossier does not define.
- `sEE`. sEE is a conjugate-linear map over the complex numbers (additive, and sending a scalar multiple c times x to the complex conjugate of c times the image of x) from the space X.EE to the space (fc X.zs).Sp.HH. The dossier shows X.EE to be a finite-dimensional complex inner product space and HH to be a type with a normed group structure and a complex inner product, taken from the field Sp of the face fc X.zs.
- `∃ d : X.MIDat fc`. The statement begins by asserting that there exists some d, an object of the type that the code calls X.MIDat fc. The dossier does not show what such an object consists of.
- `X.MIUnit2 d`. The first conjunct is a condition on d that the code calls X.MIUnit2. Its body is not shown.
- `X.MIid eV sEE d`. The second conjunct is a condition that the code calls X.MIid, and it is the only one of the three that involves the maps eV and sEE together with d. Its body is not shown.
- `X.AuNZ d`. The third conjunct is a condition on d that the code calls X.AuNZ. Its body is not shown.

The reading does not open the names `Formalism.IndefR.Cx.CxData.MIDat`, `Formalism.IndefR.Cx.CxData.MIUnit2`, `Formalism.IndefR.Cx.CxData.MIid`, `Formalism.IndefR.Cx.CxData.AuNZ` and `Formalism.IndefR.Cx.CxData.zs`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. As a suggestion only, the names and the module title (isometric periods of unit hypotheses) hint that MIDat is a package of data for a map or period identity, that MIUnit2 is a unit-type hypothesis on it, that MIid is an identity relating that data to eV and sEE, and that AuNZ is a non-vanishing condition. The typing of fc suggests that X.zs is a record of type DefSub A attached to X, although it is not among the fields of CxData shown.

The reader's confidence is low. The logical shape and the types of the arguments are fully visible, but the type of the witness d, all three conditions on it and the object X.zs have no body in the dossier, so the mathematical content of the statement cannot be seen.

The check found no error in this reading.
