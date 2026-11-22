# Independent peer review of the declaration graph and redundancy analyses

## Verdict

Both analyses accurately transcribe most numbers from their own `summary.json` files, yet both contain material bugs in their scripts and overstate key conclusions in their prose. In `verification/decl-graph/`, `build.py` overcounts source lines by one per file and omits import-visibility checks in its `names` pass, while `check_sample.py` omits both import-closure and `private` filtering in `fields` and `loose`, inflating the compiled-sample overreach from 2.61 times the real count to 6.19 times and invalidating the published evidence for the claim about the 190,721 unreached declarations. In `verification/redundancy/`, parser and resolution bugs introduce false positives into `true`, `premise`, and `forward`, corrupt the split between project and library forwards, and break the claim that 4,519 duplicate groups lie inside one namespace where names resolve identically (only 368 of the 1,568 same-module groups even belong to those 4,519, and concrete pairs inside the 4,519 state unrelated theorems). By contrast, the `RecTExists` wiring described in the redundancy README matches the source, the other two fields of `OpenLiteratureStatements` are filled by the premise-free theorem `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` with no hidden assumption or `True` shortcut in the inspected levels, and an open search across all 175,187 modules found no definition mismatch or unsound shortcut that could make the five headline theorems of `src/Main.lean` hold vacuously (though `kexactB`, `kcopy`, and one `run_tac` block bypass elaborator type checking and place full trust on the kernel).

## Task 1. Classification errors

### Sampling design

Using fixed seed `20261122`, I drew every row of the two small classes (`reflexive` with 2 rows and `true` with 3 rows), 35 random rows from each of the five larger classes (`premise`, `rfl`, `one_tactic`, `returns_premise`, `forward`) in `verification/redundancy/data/findings.tsv.gz`, 35 random groups from `verification/redundancy/data/theorems_same_statement.tsv.gz`, and 110 random unclassified theorems from the 730,014 theorems that received no class. Because the small `premise` class has only 58 rows in total and the `forward` sample exposed systemic bugs, I also audited all 58 rows of `premise`, cross-checked all 65,262 rows of `forward` against `src/` and `verification/decl-graph/data/graph.npz`, checked all 6 rows of `returns_premise` whose proof exceeds three words, and audited Group `0` (`spMap_comp₂`, 186 members) directly in `src/`.

### Summary of sample results

| Category | Total in data | Sample checked | Right in sample | Wrong in sample | Full-class errors confirmed |
|---|---:|---:|---:|---:|---|
| `reflexive` | 2 | 2 | 2 | 0 | 0 of 2 |
| `true` | 3 | 3 | 2 | 1 | 1 of 3 (`hk_mem_fixed`) |
| `premise` | 58 | 35 | 35 | 0 | 1 of 58 (`isCrys_isDR_prod`) |
| `rfl` | 22,421 | 35 | 35 | 0 | Not exhaustively checked |
| `one_tactic` | 697 | 35 | 35 | 0 | Not exhaustively checked |
| `returns_premise` | 353 | 35 | 35 | 0 | 0 in sample and 0 in the 6 four-word rows |
| `forward` | 65,262 | 35 | 32 | 3 | 528 section-variable projections, 111 `inferInstance`, 41 `by simpa using`, plus target-origin errors |
| `theorems_same_statement` groups | 65,279 | 35 | 34 | 1 | Also confirmed Group `0` mixes two distinct `spMap` definitions |
| Unclassified theorems | 730,014 | 110 | 97 | 13 missed trivial cases | 6 missed simple forwards, 2 premise projections, 5 one-argument `simp` or `simpa` proofs |

### Confirmed errors in `true` and `premise`

`scan.py` implements `conclusion()` at lines 156 to 175 by calling `top_split(rest, ", ")` and `top_split(rest, " → ")` without respecting the precedence of `∧`, `∨`, or `∀`. Whenever a theorem's conclusion is a conjunction whose final conjunct contains an implication `→`, `conclusion()` discards every earlier conjunct and treats only the text after the last `→` as the whole conclusion.

1. Wrong `true` classification (1 of 3 in the class, and the sole `true` row marked reached by `Main.lean`). File `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HkMemFixed.lean`, line 8, declaration `GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed` (291 proof words, reached by both `names` and `widest`). Quoted declaration head and tail of statement.

```lean
theorem hk_mem_fixed ... :
    hk ρ K e v ∈ fixed ρ K ∧ ∀ g : GL ι F, (∀ q : GL ι F ⧸ K, e (g * q.out) = e q.out) → True := by
```

`scan.py` strips `hk ρ K e v ∈ fixed ρ K ∧ ∀ g : GL ι F, (∀ q : GL ι F ⧸ K, e (g * q.out) = e q.out) →` and reads the conclusion as `True`. The first conjunct is a real 291-word proof that the Hecke operator lands in the `K`-fixed subspace. Because the other two `true`-class declarations (`PositivityTheory.Rg.Ming.bridge_true` in `src/Development/WeilBound/RepresentationTheoryGL/PointAveraging/MinkowskiBalls/BridgeTrue.lean` at line 12 and `UpperTheory.Lit.Dz.true_of_artin_reciprocity_of_recTExists` in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GlobalArtinReciprocityTrivial.lean` at line 15) are unreached, zero genuine `true`-class theorems are used by `Main.lean`, not 1 as reported in `verification/redundancy/README.md`.

2. Wrong `premise` classification (0 of 35 in the random sample, 1 of 58 in the full-class check, reached by both `names` and `widest`). File `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimitiveFrobeniusFixed/AdmProd.lean`, line 6, declaration `UpperTheory.V.ML.isCrys_isDR_prod` (261 proof words). Quoted statement.

```lean
theorem isCrys_isDR_prod :
    ∀ (l F r : ℕ) (L : List ℕ), AdmL l F r L →
      admitted l F r L.prod ∧ L.prod ≠ 0 ∧
      (∀ q, AdmL l F r (q :: L) → q.Coprime L.prod) ∧
      ∀ q, AdmL l F r (q :: L) → AdmL l F r L := by
```

`scan.py` discards the three substantive conjuncts (`admitted l F r L.prod`, `L.prod ≠ 0`, and coprimality) and extracts only the trailing `AdmL l F r L`, which matches the premise. Removing both false positives lowers the count of statements true by form from 61 to 59, lowers the widest-run reached count from 30 to 28, and lowers the `names`-run reached count from 28 to 26.

### Confirmed errors in `forward`

In the 35-row random sample of `forward`, 32 are genuine forwards and 3 are wrong (8.6 percent). All three errors arise from the same bug in `scan.py`. `binders(given)` collects variable names only from the declaration's own binder list and ignores `variable` declarations in scope (`ctx`). When a proof is a dot-projection on a section `variable`, its leading identifier is absent from `names`, so `forward()` mistakes the projection for a call to an external library declaration and records `forward_to_project = 0`.

1. File `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLattices.lean`, line 53, declaration `GlobalTheory.HL.CoordInnerSnd.h_e_es` (recorded with `forward_target = Fr.h_es`, `forward_to_project = 0`). `Fr : LocNG.FrameD H r` is a section `variable`. Quoted declaration.

```lean
lemma h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b
```

2. File `src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ContinuousResTSymm.lean`, line 82, declaration `GlobalTheory.MixModel.OrthDec.qB_iB` (recorded with `forward_target = d.symm.qA_iA`, `forward_to_project = 0`). `d : OrthDec S A B` is a section `variable`. Quoted declaration.

```lean
theorem qB_iB : d.qB * d.iB = 1 := d.symm.qA_iA
```

3. File `src/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/PowObjGeometricallyConnected.lean`, line 526, declaration `GlobalTheory.Serre.IsTensor.mapRight_id` (recorded with `forward_target = h.map_id`, `forward_to_project = 0`). `h : IsTensor H b G a M` is a section `variable`. Quoted declaration.

```lean
theorem mapRight_id : h.mapRight h (IsLinearHom.id a) = 𝟙 H := h.map_id
```

In addition, 1 of the 32 genuine forwards in the sample has the wrong `forward_to_project` flag.

4. File `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LengthEqLengthInvariantsOfTorsionLevels.lean`, line 260, declaration `GlobalTheory.TateLimit.red_zlTw` (recorded with `forward_target = map_mul`, `forward_to_project = 1`). Quoted declaration.

```lean
theorem red_zlTw (D : LData F Ω l) (n : ℤ) (r : ℕ) (g) (x : ℤ_[l]) :
    PadicInt.toZModPow r (zlTw D n g x) = zr D n r g (PadicInt.toZModPow r x) :=
  map_mul _ _ _
```

The proof calls Mathlib's `map_mul`, yet `scan.py` marks `forward_to_project = 1` because 14 unrelated project declarations happen to end in `.map_mul`. One other sampled row, `GlobalTheory.Vert.Flag.π_quotTwoGr₀` in `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagPairTwoStepExchange.lean` at line 66 (`cokernelZeroIsoTarget_inv.symm`), applies `.symm` to a Mathlib lemma rather than forwarding it unchanged.

Auditing all 65,262 `forward` rows in `findings.tsv.gz` against `src/` and `verification/decl-graph/data/graph.npz` shows four systematic errors across the class:

- 528 rows have a `forward_target` whose root identifier is a section `variable` in scope (for example `π.continuous_orbit'`, `T.sq_sq`, `E.hom.map_one`, `Fr.h_es`, `d.symm.qA_iA`, `h.map_id`). None of these forwards a named declaration, yet all 528 are counted in `forward` and in the 5,241 `to_a_library_declaration` bucket.
- 111 rows have `forward_target = inferInstance` and `forward_to_project = 0`. `inferInstance` invokes typeclass synthesis in term mode and belongs with tactic automation rather than library-theorem forwarding.
- 41 rows have proofs of the form `by simpa using X ...` (for example `GlobalTheory.W1.IsGal.act_one` in `src/Development/AbelianVarietyTheory/Definitions/Divisors/IsGaloisCover.lean`, `by simpa using GlobalTheory.ZM.IsGaloisCover.one h`). `simpa` runs the simplifier on both the goal and the hypothesis rather than merely passing `X` through.
- Cross-checking `forward_to_project` against `decl-graph`'s `strict` edges shows two offsetting misclassifications. Among the 4,834 bare-name targets marked `forward_to_project = 1`, 525 have no matching `strict` project edge and are standard Mathlib lemmas colliding with unrelated project last names (`map_add` 54, `map_mul` 43, `map_zero` 42, `map_one` 32, `map_sub` 32, `norm_nonneg` 26, `continuous_snd` 21, `lift_fst` 19, `map_smul` 18, `star_star` 17). Conversely, among the 5,241 rows marked `forward_to_project = 0` ("comes from Lean or Mathlib"), 175 have a dotted target whose prefix is a `strict` project declaration (such as `continuous_adeleCoordEquiv_symm.measurable`, `isCompact_unitBall.measure_lt_top.ne`, `mem_riemannRochSpace_iff_regularAt_everywhere.symm`, and `mk_eq_mk.mpr`). Combining the 528 variable projections, 111 `inferInstance` proofs, and 175 project-declaration dot-projections shows at least 814 of the 5,241 library forwards (15.5 percent) are misclassified.

### Notes on `reflexive`, `rfl`, `one_tactic`, and `returns_premise`

All 2 `reflexive`, 35 `rfl`, 35 `one_tactic`, and 35 `returns_premise` sampled rows satisfy `scan.py`'s syntactic criteria. Two prose qualifications apply. First, `verification/redundancy/README.md` at line 30 describes the `rfl` class as proofs "which Lean accepts when the claim holds by definition", whereas `RFL` also includes `le_rfl`, `le_refl _`, `Subset.rfl`, `subset_rfl`, `trivial`, `⟨⟩`, `by constructor`, and `True.intro`, which hold by preorder reflexivity, set reflexivity, or `True.intro` rather than definitional equality alone. Second, many `returns_premise` rows in the 35-item sample (such as `GlobalTheory.GKUnitaryRankOne.mem_intL` and `Formalism.L2.SG.MassDataConc.inTypedC_of`) are definitional bridges where the premise's type unfolds to the goal's type rather than syntactic tautologies of the form `(h : P) : P := h`. All 6 rows of `returns_premise` with four proof words were checked in `src/` and proved to be `fun h => h`.

### Confirmed errors in `theorems_same_statement`

Of the 35 random duplicate groups sampled from `theorems_same_statement.tsv.gz`, 19 are forwarding pairs (such as `*Statement` wrappers) and 16 are non-forwarding duplicate groups. All 19 forwarding pairs and 15 of the 16 non-forwarding groups were verified in `src/` and `graph.npz` to resolve every project identifier in their statements to the same definitions. One group in the 35-group sample is wrong.

- Group `60467` (2 members, both reached by `names` and `widest`). Member 1 is `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_extension_GL_same_place` in `src/Formalism/LocalToGlobal/GlobalTheory/GL6/ComplementSmulLocalExtensionMatrix.lean` at line 174. Member 2 is `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.local_extension_GL_same_place` in `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/ComplementSmulLocalExtensionMatrix.lean` at line 175. Both files quote the same text statement.

```lean
theorem local_extension_GL_same_place (M : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    bc (prV (E := E) v) (localExtensionGL v M) = M := by
```

Inspection of `src/` shows that the second file is a copy of the first placed inside namespace `S0`, defining its own distinct constant `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.localExtensionGL` rather than referring to `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.localExtensionGL`. Because those are two distinct Lean constants, the two theorems do not state the same proposition in Lean.

Direct inspection of Group `0` (`spMap_comp₂`, 186 members, highlighted at lines 140 to 147 of `verification/redundancy/README.md`) also refuted the README's statement that `spMap` is defined in three modules and that the text does not show which copy is meant. `spMap` is defined as a `def` or `abbrev` in six modules (plus a seventh `theorem` `GlobalTheory.SubClosure.IsPt.spMap`), and the `open` directives in the 186 files identify the target unambiguously. Specifically, 179 members open `ReciprocityTheory.ChartRestriction.G.Geo.Tor` (where `spMap` is `Spec.map (CommRingCat.ofHom f)`), whereas 7 members open `GlobalTheory.EtC` (where `GlobalTheory.EtC.spMap` in `src/Development/AbelianVarietyTheory/Definitions/Divisors/GalMapMul.lean` at line 133 is `sch.map (Spec.map (CommRingCat.ofHom f))`). Group `0` therefore merges 179 theorems about `Tor.spMap` with 7 theorems about `EtC.spMap`.

### Unclassified theorems (110 random sample)

None of the 110 random unclassified theorems matched `scan.py`'s exact syntax for `reflexive`, `premise`, `true`, `rfl`, or `one_tactic`, which shows the parser did not drop exact matches on this sample. However, 13 of the 110 (11.8 percent) are one-step forwards, direct premise projections, or single-argument `simp` or `simpa` proofs that fall just outside `scan.py`'s rigid patterns, plus 2 borderline one-line unfolding lemmas (`Formalism.L2.SG.NormCut.resT_of_mem` in `src/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LeviMul.lean` at line 19, `by unfold resT; rw [dif_pos hz]`, and `GlobalTheory.DefTransfer.cj_apply` in `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsStableComplBot.lean` at line 24, `by simp [cj, MulAut.conj_apply]; rfl`). The 13 clear missed cases are listed below.

Missed one-step forwards (6 cases, blocked only by a dot-projection argument, a leading `fun` binder, parentheses before a dot suffix, or a compound argument):

1. `src/Formalism/SharpRestriction/CuspSpanNormBounds/LatticeGluingRadicals.lean`, line 4837, `Formalism.MainNotions.LatticeGluingRadicals.i_mem_dual`. Proof `Formalism.HermitianLatticesTheory.dualBasic_mem_dual S.hT L x`.
2. `src/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/FStarOmRepPf.lean`, line 100, `Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OmR.qu_of_det`. Proof `fun _ hd h0 => eq_zero_of_orth F.fl F₁.fl h hd h0`.
3. `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsCuspidalIffCompositions.lean`, line 57, `GlobalTheory.Parabolic.unipRadical_le_blockTri`. Proof `fun _ hu => blockTriangular_of_sub_one hu`.
4. `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/SquareIntegrableGammaZetabarInv.lean`, line 1678, `Formalism.FourierDecayAlt.P.MAx2.J0.ev_zb`. Proof `coordE_vzb q.1`.
5. `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AcrisFrobeniusFixedEqPadicInt.lean`, line 209, `GlobalTheory.MemLoc.PhiFix.phiA_alg`. Proof `(GlobalTheory.CrisMaps.phiA_extends l).alg a`.
6. `src/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean`, line 112, `GroundTheory.Heights₂.Heights.PointwiseLelong.volume_sphereBall_ne_top`. Proof `(volume_ballProd_lt_top (HermNorm.std N) 1).ne`.

Missed direct premise projections (2 cases):

7. `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LiteratureResults/KTheoryStability/ReductionBoundsTorsion/ArithmeticGapBounds/AeEqCosetAvgOfMemInvariantSubspace.lean`, line 102, `PositivityTheory.KB.SpectralGap.PGap.u_int_eq`. Proof `(((((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').2 u hm hu).2 hint).2` (pure nested `.2` projection of section variable `hU`).
8. `src/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsIsClosedImmersionGenericPoint.lean`, line 140, `GlobalTheory.Weight.IsCInf.dual`. Proof `fun i y hy => (h i y hy).neg`.

Missed one-argument `simp` or `simpa` proofs (5 cases, intentionally outside `ONE_TACTIC` except for `simpa` which only missed `-1` as a literal):

9. `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean`, line 29, `PI.OmVe.ffH_zero_left`. Proof `by simp [ffH]`.
10. `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClOfSelf.lean`, line 20, `GlobalTheory.CompanionTheory.WordProd.clOf_self`. Proof `by simp [clOf]`.
11. `src/Development/AutomorphicSpectrum/Proofs/MetricProofs/ZeroWeightRegularFamily.lean`, line 15, `GlobalTheory.CompanionTheory.Ar.Giv.levi_const_zero`. Proof `by simp [levi]`.
12. `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean`, line 72, `ReciprocityTheory.ChartRestriction.G.Chart.scaleS_snd'`. Proof `by simp [scaleS]`.
13. `src/CompanionTheory/AutomorphicTheory/PieriRules/ThetaBesselIsometries/ComplexifiedDerivedActionLieHomGramAdjoint.lean`, line 131, `Gp91.GlobalTheory.ComplexifiedAction.dsig_neg_left`. Proof `by simpa using dsig_smul_left R (-1) hX hv`.

## Task 2. Figures and conclusions

### Recomputation of `verification/decl-graph/README.md`

Recomputing directly from `verification/decl-graph/data/declarations.tsv.gz`, `modules.txt.gz`, `graph.npz`, `summary.json`, and `sample-check.json` confirms that every declaration count, theorem count, module count, reachability share, library row, and compiled-sample table entry printed in `verification/decl-graph/README.md` matches its corresponding JSON and data files (1,061,531 declarations, 818,755 theorems and lemmas, 175,187 modules, 776,843 to 870,810 reached declarations, 190,721 unreached declarations, 21,126 unreached modules, 15,347 globally tagged declarations or instances among real declarations, and 135 public name clashes). Five concrete factual or script errors nevertheless distort the README's figures and commentary.

1. Phantom line counts (+1 per file). `verification/decl-graph/build.py` at line 232 computes each module's line count as `raw.count("\n") + 1`. Every one of the 175,187 `.lean` files under `src/` ends with a trailing newline (`0` files omit it). As a result, `decl-graph/README.md` overcounts total lines as 17,549,402 instead of the true 17,374,215 (off by 175,187 lines, contradicting `verification/NOTES.md`), overcounts the 21,126 unreached modules as 1,524,285 lines instead of 1,503,159 (off by 21,126 lines), and overcounts the 2,681 `XCSqsys` sample modules as 329,322 lines instead of 326,641 (off by 2,681 lines).
2. Misdiagnosis of the 135 public name clashes. `decl-graph/README.md` at lines 112 to 113 asserts that "Lean refuses a second declaration of a name, so each of the 135 is a misreading of at least one declaration." Auditing all 135 clashes in `declarations.tsv.gz` shows that every single one is a `theorem` (124) or `lemma` (11) in a distinct module (`0` inside the same module and `0` `def`, `abbrev`, `structure`, `class`, `instance`, or `inductive` declarations). Direct inspection of four clashing pairs proves they are genuine, standard public declarations rather than parser errors by `build.py`. Specifically, `Bl.general_b_fact.goal1` appears verbatim in `src/Lemmata/GeneralBFact/Imports.lean` at line 8 and `src/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/GeneralBFact.lean` at line 8 (two byte-for-byte identical 25-line files), `ReciprocityTheory.PGsh.DualPair.π_η` appears publicly in `src/ReciprocityTheory/DualLattices/IsFibreSq.lean` at line 39 and `src/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean` at line 141, `PositivityTheory.Rg.Sw.AbsSt.mR_mul` appears publicly in `src/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/NormDetFirstBlockCompact.lean` at line 22 and `SphericalSectionContinuousNeZero.lean` at line 70, and `Formalism.FourierDecayAlt.P.theorem_S_of_steps` appears publicly in `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean` at line 2590 and `InterpolationInverseMatrixSumIdentity.lean` at line 858 (both imported together in `QNFAsm.lean`). Because `build.py` uses `PUB.setdefault(name, i)`, it keeps only the first copy in topological order and redirects every `names` reference there, which can make second copies look unreached.
3. Missing import-visibility check in `build.py`'s `names` pass. `decl-graph/README.md` at lines 23 to 29 states that `names` resolves names as Lean does and that a declaration is visible from a module only when its module is in the import closure. In `build.py` at lines 273 to 309, however, `resolve()` looks up `PUB.get(n)` globally without checking `g.closure` (import visibility is checked only inside `follow()` for `fields` and `loose`). On the 2,681-module `XCSqsys` sample alone, 835 of 95,839 `strict` edges jump completely outside the 2,681 sample modules and another 2,583 jump to unimported modules inside the sample.
4. `scoped instance` counted as global automation. `decl-graph/README.md` at lines 33 to 35 says automation includes every instance and tactic attribute unless marked `local`. In `build.py`, `attr_class()` checks only `"local" in mods.split()`, so all 220 `scoped instance` declarations in `src/` are seeded globally into `g.auto` even though Lean activates them only inside `open scoped`. In addition, `g.auto` contains 16,151 records in total (15,347 real declarations plus 804 global `attribute` pseudo-records).
5. Omitted library and invisible generated declarations. The library table omits `BuildAid` (5 files, 0 real declarations, 5 `run_cmd` pseudo-records), and both `build.py` and `scan.py` omit `*Cpt` declarations generated programmatically via `addDecl` by `cpt_copy_thms` in `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutMainCpt.lean` (parsing only the 24 textual declarations in that file).

### Recomputation of `verification/redundancy/README.md`

Recomputing directly from `verification/redundancy/data/findings.tsv.gz`, `theorems_same_statement.tsv.gz`, `definitions_same_text.tsv.gz`, and `summary.json` confirms that all main table figures match their underlying files (1,057,878 declarations, which equals `1,061,531` minus 106 `alias` and 3,547 unnamed `instance` declarations, 818,755 theorems, 88,741 with any class, 65,262 forwards split into 39,732, 20,289, and 5,241, 65,279 duplicate theorem groups with 78,892 extra copies, 14,682 same-proof groups with 18,935 extra copies, 26,802 non-forwarding groups with 37,924 extra copies and 29,706 reached extra copies, 5,520 duplicate definition groups with 7,443 extra copies, median proof length of 36 words with 94,387 proofs of at most 5 words and 41,772 over 500 words, and 52 of 58 `premise` theorems also returning their premise). Four prose numbers or claims are wrong.

1. The `4,519` and `1,568` namespace claim (`verification/redundancy/README.md`, lines 163 to 165) fails in three separate ways. The README states that "Of the 65,279 duplicate groups, 4,519 lie inside one namespace, and 1,568 of those inside one module. In those 4,519 groups the names resolve the same way." First, the exact figure `4,519` arises from evaluating `len({n.rsplit(".", 1)[0] for n in names}) == 1` on `theorems_same_statement.tsv.gz`. For a root-namespace declaration with no dot, `n.rsplit(".", 1)[0]` returns the declaration's own bare name `n` rather than an empty namespace string. That bug adds 3,219 dotted same-prefix groups to 1,300 root-level groups whose members share an identical bare name (such as `private theorem loc_of_int` across distinct files) while excluding 403 root-level groups whose members have different bare names (the true same-prefix count is 4,922, or 3,219 excluding the root namespace). Second, 1,568 is the total number of single-module duplicate groups across all 65,279 groups, not a subset of the 4,519. Only 368 of the 1,568 single-module groups belong to the 4,519, while 1,200 single-module groups span multiple namespaces or prefixes inside one file (for example Group `4923` in `TwistedPeriodIdentityLocal.lean`). Third, names do not resolve the same way inside the 4,519 groups. Cross-checking `graph.npz` found 17 groups inside the 4,519 where the same short identifier resolves to different project definitions across members. In Group `46219`, both `UpperTheory.quotient_measure_split` (`src/Development/AutomorphicArithmetic/AdelicQuotients/QuotientMeasureSplit.lean`, line 39) and `UpperTheory.rational_splitting_exists` (`src/Development/AutomorphicArithmetic/CommutativeAlgebra/RationalSplittingExists.lean`, line 29) lie in the same non-root namespace `UpperTheory` and share the exact text statement `: SplitQ`, yet the first file opens `UpperTheory.ConvolutionTheory.T4` (a Haar-measure quotient identity) and the second opens `UpperTheory.Gal.Int.Geo` (a finite-index splitting lemma about `Fin D.m`).
2. `spMap` definition count and resolution (`verification/redundancy/README.md`, lines 141 to 142). As verified in Task 1, `spMap` is defined as a `def` or `abbrev` in six modules rather than three, and the `open` directives in the 186 files identify which definition each copy uses (179 resolve to `Tor.spMap` and 7 resolve to `EtC.spMap`).
3. Statement-class counts (`verification/redundancy/README.md`, lines 5 to 6, 69, and 91). Removing `hk_mem_fixed` (`true`) and `isCrys_isDR_prod` (`premise`) reduces the count of statements true by form from 61 to 59, reduces the widest-run reached count from 30 to 28, and leaves 0 genuine `true`-class theorems reached by `Main.lean`.
4. Forward target split (`verification/redundancy/README.md`, lines 75 to 79). As quantified in Task 1, 525 bare-name rows in the 60,021 project-forward count lack any matching `strict` project edge (Mathlib collisions), while at least 814 of the 5,241 library-forward rows are section-variable projections (528), `inferInstance` (111), or project-declaration dot-projections (175).

### Evaluation of the three prose conclusions

#### Conclusion 1. "The 190,721 unreached declarations of the whole project are more likely too few than too many"

The check reported in `verification/decl-graph/README.md` (lines 71 to 107) does not support this conclusion because `check_sample.py` does not test `build.py`'s actual reachability algorithm. Two bugs dominate the compiled-sample numbers in `sample-check.json`. First, because `build.py`'s `resolve()` ignores import visibility and `check_sample.py` never restricts `text_strict()` to the 2,681 sample modules, 516 of the 2,925 declarations reached by `names` (80.0 percent of the 646 `text_beyond_exact`) lie outside the 2,681 compiled sample modules altogether (for example in `Formalism.FrobeniusOrbits.Statement` and `Formalism.LocalRingCardinality.Params`). Inside the 2,681 sample modules, `check_sample.py`'s `names` run reaches only 2,409 declarations (2,279 true positives, 130 false positives, 141 false negatives), which is fewer than the real 2,420 and directly refutes the README's claim that "Every way reaches more than is really reached. The names way reaches 2,925, which is 1.2 times the real 2,420." Second, `check_sample.py`'s `text_reach()` (lines 111 to 134) omits both the `g.closure` import-visibility filter and the `private` filter that `build.py`'s `reach()` applies at lines 360 to 361 (and omits `g.always` and non-real `g.auto`). Re-running `build.py`'s actual `reach()` algorithm on the `XCSqsys` 2,681-module subgraph yields the comparison below.

| Mode | `check_sample.py` total (outside sample) | `build.py` `reach()` clipped to sample | `build.py` `reach()` with import-visible `strict` | Ratio of clipped `build.py` to 2,420 | Ratio of `check_sample.py` to 2,420 |
|---|---:|---:|---:|---:|---:|
| `names` | 2,925 (516) | 2,382 | 2,358 | 0.98x | 1.21x |
| `names+automation` | 5,432 (719) | 4,902 | 4,877 | 2.03x | 2.24x |
| `fields` | 5,346 (554) | 3,145 | 3,123 | 1.30x | 2.21x |
| `fields+automation` | 7,801 (740) | 5,902 | 5,880 | 2.44x | 3.22x |
| `loose` | 13,519 (748) | 3,968 | 3,933 | 1.64x | 5.59x |
| `loose+automation` | 14,979 (768) | 6,316 | 6,284 | 2.61x | 6.19x |

`check_sample.py` inflated `loose+automation` by 8,663 declarations (from 6,316 to 14,979) and inflated `loose` alone by 9,551 declarations (from 3,968 to 13,519). Because the "missed 1 in 2,420" recall figure also came from that overly permissive `text_reach()` implementation rather than `build.py`'s actual `reach()`, the true false-negative rate of `build.py` on `XCSqsys` was never measured. Two further facts weaken the extrapolation from `XCSqsys` to the whole project. First, `sample-check.json` itself records that 24,701 of the 120,983 exact edges (20.4 percent) were missed by `names`, `fields`, `loose`, and `automation` combined, a finding omitted from the README. Second, `XCSqsys` is unrepresentative of the whole graph, containing 1.9 percent of project lines, zero macros or tactics, and a much higher fraction of unused declarations (2,420 of 23,043 = 10.5 percent used, so seeding 748 global instances creates a large relative jump, giving a `loose+automation` to `names` ratio of 2.65x even under true `build.py`, compared with 1.12x on the whole project where `870,810 / 776,843 = 1.12`). Because even the corrected `build.py` widest run still over-reaches `XCSqsys` by 2.60x to 2.61x and global automation seeds 15,347 declarations across the repo, the true unreached count may still exceed 190,721, yet the cited six-fold blowup and 1-in-2,420 miss rate are invalid evidence for that claim.

#### Conclusion 2. "The duplicate counts can be too high" while "the class counts of the first table can therefore be too low"

The first half is confirmed and even stronger than the README recognizes. Duplicate counts can be too high not only outside the 4,519 subset (as seen in sampled Group `60467` and in Group `0` `spMap_comp₂`), but also inside the 4,519 subset itself (as proven by Group `46219` `SplitQ`). At the same time, textual statement comparison can also miss duplicates with reordered binders, differing implicit brackets, or moved premises, so duplicate counts have errors in both directions.

The second half is wrong as an unqualified characterization of the class counts as lower bounds. While 13 of our 110 unclassified theorems confirm that `scan.py` misses many simple forwards, premise projections, and single-argument `simp` proofs, the README overlooks false positives in three of the seven classes. For `true` (1 of 3 wrong, 1 of 1 reached wrong) and `premise` (1 of 58 wrong), the published counts exceed the true syntactic-tautology counts under `scan.py`'s own definitions. For `forward`, 528 section-variable projections, 111 `inferInstance` proofs, and 41 `by simpa using` proofs inflate the count in the opposite direction to the missed forwards, so 65,262 is neither a strict lower bound nor a strict upper bound.

#### Conclusion 3. "Removing a duplicate saves its source lines and one proof check. Every theorem that the final proof depends on through other statements stays in place, so the removal shortens the project and leaves the argument as long as it was"

This conclusion holds for the 39,732 same-statement forwarding wrappers (such as `*Statement` files), where deleting the wrapper removes only a renaming indirection. It fails for the 26,802 non-forwarding duplicate groups (37,924 extra copies, of which 21,651 have different proof text from the group's first member and 29,706 are reached by the widest run). Many non-forwarding duplicates are independent alternative proofs or copy-pasted parallel modules with their own private helper lemmas. Measuring this directly on `verification/decl-graph/data/graph.npz`, among the 27,765 reached-by-names extra copies in non-forwarding duplicate groups, 4,820 copies have at least one exclusive immediate `strict` child (in-degree 1 among reached declarations), totaling 7,666 immediate exclusive helper declarations (for instance `WlocSk.HM.hpk_sq`, `WlocSk.PtD.hpk_sq`, and `PI.ComplexConjugateDerivative.hpk_mul_self` each own 4 immediate exclusive helper declarations). Deduplicating such a theorem by replacing one copy's proof with a call to another copy orphans those private helper chains as well, shrinking the dependency DAG beyond a single theorem and proof check. If "length of the argument" means critical-path depth rather than DAG size, the README's wording conflates the two and makes the false intermediate claim that every other theorem depended upon through other statements stays in place.

## Task 3. The RecTExists chain and OpenLiteratureStatements

### Attempt to refute the redundancy README's `RecTExists` claim

Every wiring claim made in `verification/redundancy/README.md` at lines 108 to 122 holds in `src/` and could not be refuted:

- `UpperTheory.One.M.New.llOf_alt` in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LlOf.lean` at lines 18 to 21 has type `RecTExists → LocalConverseGL → ... → BernsteinZelevinskyFiniteness → RecTExists` and proof `fun h _ _ _ _ _ _ _ _ _ _ _ => h`. It is reached by both `names` and `widest` in `declarations.tsv.gz`.
- `GlobalTheory.T.recTExists_of_published_inputs` in `LocalLanglandsOfHyp.lean` at lines 12 to 13 forwards `llOf_alt`, `localLanglandsGL_and_purity_at_member_alt` in `LocalLanglandsGLAndPurityAtMember.lean` at line 21 calls `recTExists_of_published_inputs`, and `GlobalArtinReciprocity` lives in `GlobalTheory.Published`.
- `UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop` in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean` at lines 215 to 218 has three fields, with middle field `localLanglandsExists : _root_.UpperTheory.Zero.LLC.RecTExists`, which `local_langlands_gl_recT_exists_of_literature` passes into `llOf_alt`.
- `UpperTheory.FinalTheorems.everyCharacter_of_row` in `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean` at lines 7 to 8 constructs `⟨h, UpperTheory.Zero.LLC.recTExists, h⟩` of type `OpenLiteratureStatements`, filling `localLanglandsExists` with `UpperTheory.Zero.LLC.recTExists`.
- `UpperTheory.Zero.LLC.recTExists` in `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean` at lines 20 to 66 takes no premises and proves `RecTExists` from `artEx`, `cuspEx` (combining `goodMap` and `junkEx`), `exists_isLExt` (applied to premise-free `Pr.exh` and `Pr.multi` from `Multi.lean`), `extDim`, `extTw`, `extDual`, `extInj`, `extDepth`, and `typeIff`.

One mathematical nuance deserves noting even though it does not contradict the README's wiring claim. `UpperTheory.Zero.LLC.IsRecT` and `LawsT` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean`, lines 20 to 72) formalize a restricted Local Langlands correspondence whose deeper compatibility fields (`twist`, `central`, `dual`, `inj`, `depth`) are gated by `Good x` (cuspidal support consisting of `GL₁` characters or depth-zero twists over `ℚ_g`). On non-`GoodCusp` supercuspidals, `CuspEx.lean` assigns arbitrary irreducible Weil-Deligne representations via `junkEx`. That restriction is sound as long as downstream proofs invoke the gated fields only on `Good` representations, yet `RecTExists` is narrower than the full Harris-Taylor or Henniart theorem for general `GL_n`.

Separately, `EveryCharacterOfLiteratureOfVWin.lean` contains two benign `True` placeholders in nearby wrapper lemmas. `siegel_eisenstein_simple_pole` at line 505 proves `GlobalTheory.Published.UnusedSlot72` (an `abbrev` for `True`) via `trivial`, and `doubling_method` at line 372 passes `trivial` for a `True` argument of `ResidueKilled.dm_of_two` (`DmOfHyp.lean`, line 24) while proving the substantive doubling identity and continuation from `cusp_rapid_decay_of_literature` and `siegel_eisenstein_continuation_of_literature`.

### The two other fields of `OpenLiteratureStatements`

In `EveryCharacterOfLiteratureOfVWin.lean` at lines 215 to 218, the other two fields are `caraianiLocalGlobalDual` and `galoisRepOfPolarizedPairLit`, and both have the same type `_root_.UpperTheory.One.M.Row` (which unfolds to `UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc`). In `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean` at lines 7 to 11, `everyCharacter` passes `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` as `h` into `everyCharacter_of_row`, which places `h` into both fields (as well as into `UpperTheory.One.vwin_of_row h`).

`UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` is declared in `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean` at lines 6 to 7.

```lean
theorem galoisLocalGlobalStrong_recParameter : UpperTheory.One.M.Row :=
  galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK
```

It takes **no premises**. Tracing its proof four levels down gives the following chain:

1. Level 1 (`RowSrc.lean`, lines 6 to 7). Applies `galoisRepresentations_of_thetaLift` to `UpperTheory.TP.K.tLiftK`. `UpperTheory.TP.K.tLiftK` (`ThetaParseval/ThetaKernels/TLiftK.lean`, line 4) forwards `UpperTheory.TP.tLift_holds_k` (`TPGHolds.lean`, line 58), which calls `tLift_of_tools_k` (`TPGTop.lean`, line 46) on `tools_holds_k` and `hgtEx_of_k stab2Cpt_k`. `Tools_k` (`GalTPDefs.lean`, lines 27 to 41) is a 14-field `Prop` hypothesis structure, and `tools_holds_k` (`TPGHolds.lean`, lines 39 to 57) constructs every field from proved project theorems without unproved premises.
2. Level 2 (`IntegralStructures/GaloisRepresentationsOfThetaLift.lean`, lines 6 to 7). Calls `galoisLocalGlobalStrong_of_geometry_lift UpperTheory.Gal.Int.Geo.geoOne_holds up`. `geoOne_holds` (`GeometricFlagBases/WeightOneGeometricRealization.lean`, line 11) calls `geometricRealization_of_weightOne` (`GeometricRealizationOfWeightOne.lean`, line 25), proved via `GeoOneOfParts.lean` and the 358-line Lefschetz fixed-point proof in `EtaleClopenDescent/LefschetzFixedPointFiniteEtaleCorrespondence.lean`, with no premises.
3. Level 3 (`IntegralStructures/Development.lean`, lines 27 to 31). Calls `UpperTheory.GalStar.Row0.row0b` (`TypeConditions/WeightsConjBis.lean`, line 84, restricting `IsQp` to `IsQpBig`) on `galoisLocalGlobal_of_geometry_lift geo up`, which equals `rest (coreAll_of (seedFinOdd_of_geoOne geo) (congFinOdd_of_ex wtLacEx_holds) up)`.
4. Level 4 (`IntegralStructures/Development.lean`, lines 20 to 28).
   - `rest` composes `galoisLocalGlobal_of_localGlobalCompatibility` (`InertCharpoly/GaloisLocalGlobalOfLocalGlobalCompatibility.lean`, line 192) with `galoisCompat_unlinkedSupport_of_spherical` (`SphericalGaloisCompatibility/GaloisCompatUnlinkedSupportOfSpherical.lean`, line 10, using premise-free `inq_holds`) and `localGlobalCompatAtIwahoriFixed_of_unlinked` (`PAdicSplitting/LocalGlobalCompatAtIwahoriFixedOfUnlinked.lean`, line 18, using `mixedOf`, `toTor_holds`, `drDesc`, and `UpperTheory.Zero.LLC.recTExists`).
   - `coreAll_of` composes `coreAll_of_core` (`CrystallineInputs/CoreAllOfRowStarCore.lean` and `CoreAllOfRowStarCoreInp.lean`, instantiating the 11-field `Prop` structure `Inp` in `OfInputs.lean` with the premise-free package `inp_holds` in `InputsOf.lean` and `Crys.lean`) with `toCoreK` (`CrystallineDescent/ToCoreK.lean`, assembling `LimOddOfLimFinOdd.lean`, `TwoUpOKOfSteps.lean`, `ClosedPhiHolds.lean`, `BcBackOffT.lean`, `LimFinOddOf.lean`, `CongFinOddOfLvLac.lean`, `MainFin.lean`, and `LadicWeightEmbeddingOverPlace.lean`).

Across all inspected levels and leaf definitions (`Row0b`, `Row0`, `PropsB`, `AboveB`, `AwayB`, `CuspSub`, `IsRegAlg`, `PolarizedPair`, `CoreAll`, `InScope`, `IrrGL`, `WD`, `IsPlaceOver`, and `TLift_k`), I found no uninstantiated structure of hypotheses, no premise equal to the conclusion, no `True` placeholder substituting for a required theorem, and no vacuous definition. Every intermediate hypothesis bundle encountered (`Tools_k`, `Inp`, `Steps`, `KSAll`) is instantiated inside the proof with premise-free theorems.

## Task 4. Open search for vacuous or unsound shortcuts

### Headline statement types and top-level deduction

All five headline theorems in `src/Main.lean` (`riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, and `LFunction_eq_zero_re_of_isPrimitive`) take their statement types from `Mathlib` (for `RiemannHypothesis`) and from `src/Statements.lean` (which imports only `Mathlib` and matches `src/Challenge.lean` line for line). A full scan over all 175,187 `.lean` files (excluding `Challenge.lean`) found zero redefinitions or shadowings of `RiemannHypothesis`, `riemannZeta`, `DirichletCharacter`, or `completedRiemannZeta`. The 2 `def` hits for `LFunction` (`GJLocalZeta.lean` and `HeckeLFunction.lean`) and 15 `def` or `theorem` hits for `IsPrimitive` live in unrelated namespaces and do not shadow Mathlib's `DirichletCharacter.LFunction` or `DirichletCharacter.IsPrimitive`.

Reading the top-level deduction chain (`src/Main.lean`, `src/Supplements/Kernels/MainTheorems.lean`, `src/Formalism/GammaFactorNonvanishing/CritLine.lean`, `RhOfRight.lean`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`, `Imprimitive.lean`, `EveryCharacter.lean`, and `ExplicitFormulaErrorOfHostConditions.lean`) confirms that the step from `UpperTheory.EveryCharacter` to all five statements uses Mathlib's `riemannZeta`, `DirichletCharacter.LFunction`, `completedLFunction`, and real division `1 / 2` compared with `s.re`. As a side note on dead imports, `MainTheoremsAll.lean` and `MainTheoremsCritical.lean` import four `SmallClassNumbers` modules (`CorGKOf`, `ClassNumberThree`, `LenEqZeroIff`, `OnePoint`) whose declarations `Main.lean` never calls, and `UpperTheory.FinalTheorems.riemannHypothesis` in `MainConclusion.lean` at line 13 is unused by `Main.lean`.

### Independent scan for risky constructs and `NOTES.md` count checks

Streaming across all 175,187 `.lean` files (excluding `Challenge.lean`) independently confirmed `verification/static-scan.txt` on the core soundness and metaprogramming counts:

- There are 0 occurrences of `axiom`, `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `skipKernelTC`, and `addAndCompile`.
- All 1,722 notations are `local` (1,721) or `scoped` (1), with 0 global notations.
- Five `modifyEnv` calls appear in `src/BuildAid/D1.lean` through `D5.lean`, each adding one namespace string to `Lean.LibrarySuggestions.nameDenyListExt`.
- Two `addDecl` calls appear in `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean`, invoked once by `cpt_copy_thms` in `CutMainCpt.lean`, which passes every copied declaration through Lean's kernel.
- Thirty-seven occurrences of `set_option allowUnsafeReducibility` appear across 33 files (an elaborator unfolding flag that does not bypass the kernel), alongside 1 `@[positivity]` extension (`EvalFrameOrd.lean`).

I also verified `NOTES.md`'s claim that every one of the 175,187 files lies in the import closure of `Main` (once apostrophes in module names such as `HypothesesZ'` and `HypothesesZ''` are allowed).

### Audit of `kexactB`, `kcopy`, and `run_tac`

- `kexactB` (`src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean`, lines 5 to 8) elaborates a term `e` with expected type `none` (`Term.elabTermAndSynthesize e none`) and closes the goal directly via `g.assign (← instantiateMVars v)` without running the elaborator's definitional-equality check against the goal. Counting across all 175,187 files found a minor count error in `verification/NOTES.md` at line 57, which reports 67 files. In fact, `kexactB` appears directly in 50 files (49 user files excluding `Imports.lean`) and via its scoped or local macros (`kc%`, `kq%`, `kd%`, `tr_clause`, `tr_via`) in 42 files, giving a union of 72 files (71 user files excluding `Imports.lean`).
- `kcopy` and `#kcopy_probe` (`src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean`, lines 15 to 65) recursively rebuild terms of `ownStruct` (`Formalism.*` structures and `And`, `Prod`, `PProd`, `Sigma`, `PSigma`, `Subtype`, `Iff`) field by field using raw `Expr.proj S i e` expressions and close the goal via `g.assign`. They appear in 4 files (`OwnStruct.lean`, `FormsRe.lean`, `HermRe.lean`, and `ExistsKeptChoiceUpperLattice.lean`), all 4 of which are reached by both `names` and `widest`.
- `run_tac` appears 32 times across 16 files rather than the 33 times reported in `verification/NOTES.md` at line 60. Thirty occurrences across 14 files run `g.revertAll` before `exact`, while two are short blocks (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FramesTildeGammaValues.lean` at line 70 using `Subsingleton.elim`, and `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsGIs.lean` at lines 81 to 83 directly calling `m.assign (← Lean.Meta.getFVarFromUserName `h)`). Both special-block files are reached by `Main.lean`.

Because `kexactB`, `kcopy`, and `m.assign` bypass only the elaborator and still submit the final declaration terms to the kernel, they cannot by themselves forge a proof under a sound kernel. However, constructing raw `Expr.proj` nodes and skipping elaborator checks specifically stress kernel soundness (and Lean `v4.33.1` lacks the `v4.34.1` runtime fixes #15241 and #15289 noted in `NOTES.md`, while including the #14576 wrong-structure projection fix), reinforcing the need for independent kernel replay on the exported proof.

### Vacuous definitions and `True` or `False` placeholders

Scanning all 175,187 files for unparameterized `def` or `abbrev ... : Prop := True` or `:= False` returned only 3 declarations, plus 1 parameterized `UnusedSlot` definition found via a separate `UnusedSlot*` scan:

- `UpperTheory.One.M.Sw : Prop := False` and `UpperTheory.One.M.TrivialCondition : Prop := True` in `src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/SwOn.lean`. Inspection of `MvAll.lean` and `UnitaryReadTrue.lean` shows these act as a compile-time switch retiring `Old.*` declarations (`False.elim s`) and enabling `New.*` declarations (`_ : TrivialCondition`), alongside empty retired-slot structures like `NTiedGPlaceholder` and `LPTiedPlaceholder`.
- `GlobalTheory.Published.UnusedSlot72 : Prop := True` (`DiscreteSpectrumResidualClassification.lean`, line 7) and `UpperTheory.GalS.UnusedSlot55 ... : Prop := True` (`TrivialLocalCondition.lean`). Inspection of their callers confirms these are unused refactoring slots rather than shortcuts for the final conclusions.
- Ninety-five `structure ... : Prop where` headers are followed by a blank line. Spot-checking four (`PoitouTateHypotheses`, `IsRegular`, `RowBase`, `Concl`) showed standard multi-field `Prop` structures whose fields begin after the blank line rather than zero-field structures.

## Verified source facts versus inferences

Everything reported above as a count, quote, file path, declaration name, bug mechanism, or graph measurement was verified directly from the source files in `src/`, the scripts in `verification/`, and the data files in `verification/decl-graph/data/` and `verification/redundancy/data/`. Two items in this report are inferences rather than direct measurements and are labeled here accordingly:

- That the true number of unreached declarations across the entire 175,187-module project may still exceed 190,721 despite the bugs in `check_sample.py` is an inference from the corrected `build.py` overreach ratio on `XCSqsys` (2.60x to 2.61x) and the 15,347 global automation seeds, because no whole-project compiled dependency graph exists on this machine.
- That Lean `v4.33.1` accepts the 135 cross-module duplicate public `theorem` and `lemma` names (as opposed to `build.py` misparsing them) is inferred from direct source verification that the checked pairs are genuine unambiguous public theorems imported by `Main` together with the reported successful compilation of `Main` by an independent run noted in `NOTES.md`.

## What was not checked

- No Lean compiler, kernel, `lean4export`, or `lake comparator` binary was run, so no proof term was type-checked and the Mathlib `v4.33.1` checkout was not inspected locally.
- The compiled `deps.tsv` file from the author's `XCSqsys` build is not in the repository, so I could not recompute exact false negatives (`exact_missing_from_text`) for the corrected `build.py` `reach()` run on `XCSqsys`.
- In Task 1, I did not exhaustively inspect all 22,421 `rfl`, 697 `one_tactic`, 353 `returns_premise`, 65,262 `forward`, 65,279 duplicate groups, or 730,014 unclassified theorems by hand beyond the reported random samples and targeted full-data audits.
- In Task 2, I did not reconstruct the full 175,187-by-175,187 module import-closure matrix across the entire project to quantify how many of the 6,959,866 `strict` edges cross outside their source module's import closure globally (this was measured exactly on the 2,681-module `XCSqsys` subgraph).
- In Task 3, I traced `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` four levels down and inspected its core definitions and intermediate hypothesis bundles, but did not trace all transitive dependencies of `tools_holds_k`, `geoOne_holds`, `inp_holds`, `toCoreK`, `inq_holds`, `toTor_holds`, or `recTExists` down to Mathlib leaves.
- In Task 4, I did not inspect every one of the 95 blank-line-headed `Prop` structures or audit all ~242,000 non-theorem definitions for subtle mathematical vacuity deeper in the dependency tree.
