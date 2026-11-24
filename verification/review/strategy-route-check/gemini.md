# Gemini Route Check of Verification Strategy Documents

This report compares every table row and reading list in [`CLAIMS.md`](../../strategy/CLAIMS.md) and the four assigned sections of [`README.md`](../../strategy/README.md) against the Lean 4 source files under `src/` according to [`route-check.txt`](../../strategy/briefs/route-check.txt). Across the 44 table rows of `CLAIMS.md`, 8 are `supported`, 5 are `says more`, 9 are `says less`, and 22 are `differs`. Five entries in the lists under the tables are contradicted by the Lean text, and Part C records the 20 most substantive findings across the four assigned sections of `README.md` alongside an independent check of the four error-bracket division terms. Because this check worked read-only on `src/` without running `lean`, `lake`, `cone.py`, or external PDFs, dependency declaration counts, Mathlib internals, and references to the external author note could not be tested.

## Part A, table of verdicts for all rows of `CLAIMS.md`

Every row of `CLAIMS.md` is listed below in order with its verdict and the Lean files and lines checked:

| Row | Verdict | Lean source reference |
|---|---|---|
| 1.1 | supported | `src/Main.lean` lines 10-11, `src/Statements.lean` lines 10-12 |
| 1.2 | supported | `src/Main.lean` lines 10-23, `src/Statements.lean` lines 7-20, `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean` lines 47-89 |
| 1.3 | says more | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` lines 15-20, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean` lines 11-16, `src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean` lines 10-28, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 21-23 |
| 1.4 | supported | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 17-20 |
| 2.1 | supported | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` lines 12-38, `src/Formalism/StatementOC.lean` lines 14-17, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean` lines 13-29 |
| 2.2 | supported | `src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean` lines 12-70, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean` lines 11-28, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean` lines 15-18, `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean` lines 30-38, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean` lines 45-70, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` lines 102-121 |
| 2.3 | differs | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 17-20, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean` lines 21-26, `src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean` lines 30-32, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean` lines 16-19 |
| 3.1 | says less | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` lines 31-38 and lines 138-140, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean` lines 92-94 and line 140 |
| 3.2 | says more | `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` lines 31-41 |
| 3.3 | differs | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` line 143, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean` lines 26-28, lines 92-96, line 138, and lines 146-148, `src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean` lines 17-27, `src/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean` lines 42-54 |
| 3.4 | differs | `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairShare.lean` lines 30-35, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean` lines 13-16, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean` lines 22-27 and lines 32-34, `src/Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean` lines 49-53 |
| 3.5 | says more | `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean` lines 45-51 and lines 104-108, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean` lines 17-18 and lines 36-40, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean` lines 37-40 |
| 3.6 | says more | `src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean` lines 13-16, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean` lines 11-15, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean` lines 350-354, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean` lines 22-28 |
| 3.7 | says more | `src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean` lines 55-58, `src/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean` lines 12-18, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean` lines 255-258, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean` lines 30-31 |
| 3.8 | differs | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean` lines 47-50, `src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean` lines 158-161 |
| 4.1 | differs | `src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean` lines 76-95 and `src/Formalism/ThickAverageLoss/PartnersToFactorsAt.lean` lines 25-34 |
| 4.2 | differs | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean` lines 204-206 and `src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean` lines 72-74, 97-100 |
| 4.3 | says less | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` lines 32-77, 287-343 |
| 4.4 | differs | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` lines 347-355 and `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean` lines 38-44, 54-56 |
| 5.1 | differs | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean` lines 41-48 and `src/Formalism/SizeWindowBrackets/SChain.lean` lines 21-23 and `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 39-78 |
| 5.2 | says less | `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 13-13, 90-90, 116-119 |
| 5.3 | says less | `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 15-15, 94-97, 130-138 |
| 5.4 | differs | `src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean` lines 60-63 and `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean` lines 46-62, 109-156, 171-193 |
| 5.5 | differs | `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 56-56, 105-111 and `src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean` lines 31-36 |
| 9.1 | differs | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean` lines 41-48 and `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean` lines 23-23, 75-77 and `src/Formalism/SizeWindowBrackets/SChain.lean` lines 37-40 |
| 9.2 | supported | `src/Formalism/LocalRingCardinality/DataParams₂.lean` lines 31-33, 232-232 and `src/Formalism/LocalRingCardinality/DataArith.lean` lines 194-196 and `src/Formalism/LocalRingCardinality/Params.lean` lines 32-34 |
| 9.3 | differs | `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean` lines 242-327 and `src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` lines 111-124 and `src/Formalism/SizeWindowBrackets/SChain.lean` lines 57-62 |
| 9.4 | differs | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` lines 355-355 and `src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` lines 121-124 and `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean` lines 242-242 |
| 6.1 | differs | `src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean` lines 67-86, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean` lines 19-37, and `src/Formalism/LocalRingCardinality/DataArith.lean` lines 64-105 |
| 6.2 | differs | `src/Formalism/LatticeSlopes/Statement.lean` lines 19-30, `src/Formalism/HarderNarasimhan/Statement.lean` lines 19-28, and `src/Formalism/HarderNarasimhan/StatementPl.lean` lines 29 and 68-69 |
| 6.3 | says less | `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean` lines 132-137, `src/Formalism/LocalRingCardinality/DataArith.lean` lines 149 and 171, and `src/Formalism/HarderNarasimhan/StatementPl.lean` lines 25 and 59-66 |
| 6.4 | differs | `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean` lines 192-277, `src/Formalism/LocalToGlobal/Columns/FiniteSumNonzeroLargeDepth.lean` lines 226-248, 419, 613-637, 1088-1097, and 1242-1245, `src/Formalism/LocalToGlobal/Columns/ColForms.lean` line 49, `src/Formalism/LocalToGlobal/Columns/RowForms.lean` line 258, `src/Formalism/LocalRingCardinality/Params.lean` line 40, and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RowsUOfColPins.lean` lines 30-99 |
| 6.5 | differs | `src/Formalism/LocalToGlobal/Columns/FiniteSumNonzeroLargeDepth.lean` lines 300-304 and 993-1079, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean` lines 220-250, and `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerChainMatricesWithNormBounds.lean` lines 63-69, 102-104, and 177-196 |
| 7.1 | differs | `src/Formalism/LocalToGlobal/Divisibility/NumbersLink.lean` lines 34-43 and 392-398, and `src/Formalism/LocalToGlobal/Divisibility/Numbers.lean` lines 159-173 and 195-196 |
| 7.2 | supported | `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean` lines 374-410, `src/Formalism/QuotientMetricDivisors/TheoremDivIneqRows.lean` lines 19 and 56-58, and `src/Formalism/LogFactorialIndices/StatementSize.lean` lines 23-24 |
| 7.3 | says less | `src/Formalism/LocalToGlobal/Divisibility/NumbersLink.lean` lines 79-80 and 428-478, `src/Formalism/LocalToGlobal/Divisibility/Numbers.lean` lines 159-162, and `src/Formalism/QuotientMetricDivisors/TheoremDivIneqRowsShift.lean` line 98 |
| 7.4 | supported | `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 13, 90, and 116-119, `src/Formalism/LocalRingCardinality/DataParams₂.lean` lines 69-75, 130-131, 228, and 236-238, `src/Formalism/LocalToGlobal/Divisibility/Numbers.lean` lines 58-72, and `src/Formalism/LocalRingCardinality/DataHost.lean` lines 143-146 |
| 8.1 | says less | `src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean` lines 192-197, `src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean` lines 502-505 and 560-564, `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 182-206, and `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean` lines 262-266 |
| 8.2 | differs | `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 34-39, 63-94, and 182-206 |
| 8.3 | says less | `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 50-61 and 153-164, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean` lines 172-200 and 223-266, `src/Formalism/HarderNarasimhan/StatementFrameF.lean` lines 30-66, and `src/Formalism/HarderNarasimhan/ShiftInvariance.lean` line 63 |
| 8.4 | says less | `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 208-211, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean` lines 287-300, `src/Formalism/SharpRestriction/GlobalSchurBounds/Chosen.lean` lines 18, 57-61, and 83-88, `src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean` lines 144-147, and `src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean` lines 513-526 |
| 8.5 | differs | `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean` lines 134-148, `src/Formalism/LocalRingCardinality/DataParamsS.lean` line 12, `src/Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean` lines 330-336, 489, and 499, and `src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean` lines 771-783, 818-820, 1051-1071, 1251-1283, and 1316-1359 |
| 10.1 | differs | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean` line 85, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShapeAlt.lean` lines 41-116, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ShapeOf.lean` lines 16-24, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 17-20, `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean` lines 16-18, `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean` lines 17-19, `src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean` lines 12-13, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` line 53, `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean` lines 102-105 |
| 10.2 | differs | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 17-18, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean` lines 15, 68-69, 95-116, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` lines 16-21 and 45-53, `src/Formalism/GaloisCohomology/Statement.lean` lines 79-82, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean` lines 8-10, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean` line 51, `src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean` line 10, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean` lines 73-77, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean` lines 35-104, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DefiniteSideCondition.lean` lines 40-50, `src/Formalism/LocalToGlobal/PtKOfReal.lean` lines 85-92 |

## Part B, findings on the claims

Each of the 36 rows whose verdict is other than `supported` is detailed below in row order, followed by the contradicted entries from the reading lists under the tables.

### Row 1.3 (says more)

Lean source checked in `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` lines 15-20, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean` lines 11-16, `src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean` lines 10-28, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 21-23.

```lean
def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True

theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
```

The definition ZeroFreeAll states without exception that for every primitive Dirichlet character ψ and every s with real part above 1/2, LFunction ψ.χ s is nonzero. In contrast, UpperTheory.Top.imprimitive includes the hypothesis χ ≠ 1 ∨ s ≠ 1 and therefore only extends nonvanishing to all Dirichlet characters with the trivial character at s = 1 set aside. By omitting that exception when stating that imprimitive extends ZeroFreeAll to all characters, the row claims more than imprimitive proves.

Corrected row text replaces the table summary with the statement below.

> The first theorem follows from `ZeroFreeAll`, which says for every primitive Dirichlet character that its L-function has no zero with real part above 1/2. The theorem `imprimitive` extends that through the Euler factors to all characters other than the trivial character at s = 1.

### Row 2.3 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 17-20, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean` lines 21-26, `src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean` lines 30-32, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean` lines 16-19.

```lean
theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)

def ChebyshevInequalityOnFamilyWindows {eps : ℝ} (Fm : Fam eps) (eD eL : ℝ) : Prop :=
  ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ (core Fm).Win → Tied Fm eD eL K cHH eK CL x

def ChebyshevInequalityOnWindows (Λ : Level) : Prop :=
  ∀ (eD eL eps : ℝ), 0 < eps → ∀ Fm : Fam eps, EFamC Λ (core Fm) → ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL →
    ∃ x1 : ℝ, ∀ x ≥ x1, x ∈ (core Fm).Win → Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

theorem level_gm_le_on_family_scales (Λ : Level) :
    ChebyshevInequalityOnWindows (Fam := FamP) (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm) Λ :=
  windowInequality_of_artinInputs (fun Fm => tiedCore_of_chainTied Fm) Λ

theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by
```

The proof of zero_free_all_of_green_v_win passes la ,= 3 / 2, matching the first sentence. The second sentence differs from what level_gm_le_on_family_scales and core_gm state in three ways. First, both theorems hold for every positive eps rather than restricting to small ε. Second, both theorems are conditional implications that neither mention Y nor prove the interval bound of 2.2 by themselves, because core_gm assumes EAtH and CoreAtH at x and level_gm_le_on_family_scales assumes EFamC and ChebyshevInequalityOnFamilyWindows (ChainTied on Fm.Win) to conclude Λ.Gm x ≤ x ^ (1 / 2 + (eD + eL + 7) * eps) only for large x in Fm.Win. Third, both theorems quantify universally over eD and eL rather than proving that the coefficient eD + eL + 7 is independent of ε, whereas the existence of eD and eL independent of ε for small ε and the window property on Fm.Win come from FamilyClassConnected via shape_closed_link_n_of_green and level_of_tiedWin.

Corrected row text replaces the table summary with the statement below.

> The proof of `zero_free_all_of_green_v_win` uses la = 3/2. For every positive ε, `core_gm` proves `Λ.Gm x ≤ x ^ (1/2 + (eD + eL + 7) * ε)` at large x assuming `EAtH` and `CoreAtH`, and `level_gm_le_on_family_scales` deduces that bound for large x in `Fm.Win` from `EFamC` and `ChainTied` on `Fm.Win`.

### Row 3.1 (says less)

Lean source checked in `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` lines 31-38 and lines 138-140, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean` lines 92-94 and line 140.

```lean
def Nt : Finset PChar := Λ.KEPT.erase PChar.one

def Gm (y : ℝ) : ℝ := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re

structure EAtH (Λ : Level) {φ : Frame} (H : HostRaw φ) (TT : Finset φ.A) (x eps C : ℝ) : Prop where
  o_eq : φ.o = Λ.o
  kept : H.KeptInXp Λ.KEPT

def TrivialOnFirstFactor {φ : Frame} (θ : φ.Char) : Prop := ∀ s ∈ φ.A0, θ (φ.tau1 s) = 1

def Xp : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = 1}

def KeptInXp (S : Finset PChar) : Prop := ∀ ψ ∈ S, ∃ θ ∈ φ.Xp, H.IsPrimOf θ ψ.χ
```

In `EAtH`, the field `kept` asserts `H.KeptInXp Λ.KEPT`, which places every character `ψ` of `Λ.KEPT` specifically into `φ.Xp` (characters trivial on `φ.A0` via `φ.tau1` that send `φ.iod` to `1`), rather than among arbitrary characters of the host, and ties `ψ.χ` to `H.dirAt θ` on numbers coprime to `H.condN` via `H.IsPrimOf θ ψ.χ`. Moreover, `Λ.Gm` sums over `Λ.Nt`, which is `Λ.KEPT` with `PChar.one` erased, alongside `Formalism.Gz y`, whereas the kept finite set of `Level` is `Λ.KEPT` and `kept` is the field name of `EAtH`.

Corrected row text replaces the table summary with the statement below.

> For every primitive character in the kept set `Λ.KEPT` (whose nontrivial part forms the sum of `Gm`), the `kept` field of `EAtH` requires a host character `θ` in the subgroup-trivial even subset `φ.Xp` (with `θ φ.iod = 1`) such that `H.IsPrimOf θ ψ.χ` holds.

### Row 3.2 (says more)

Lean source checked in `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` lines 31-41.

```lean
structure WinPair (eps Y : ℝ) (q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_lo : Y ^ (eps / 5) / 2 < Real.log q
  q_up : Real.log q ≤ Y ^ (eps / 5)
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_lo : Y ^ (eps / 5) * Real.log Y ^ 2 / 2 < Real.log d
  d_up : Real.log d ≤ Y ^ (eps / 5) * Real.log Y ^ 2
  d_q : q ∣ d + 1
  d_small : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → p ∣ d + 1
```

The structure `WinPair` is a proposition on `eps`, `Y`, `q`, and `d` and does not mention any host record (`HostRaw`, `HostAx`, or `Host`), so claiming that the host depends on `q` and `d` goes beyond `WinPair` itself (that connection is made in `HostRaw`, `fieldChi`, and `supplyOfAdmOf`). In addition, `WinPair` uses strict lower inequalities (`<`) in `q_lo` and `d_lo` and non-strict upper inequalities (`≤`) in `q_up` and `d_up`.

Corrected row text replaces the table summary with the statement below.

> The condition `WinPair` on `eps`, `Y`, `q`, and `d` states that `q` and `d` are primes with `q ≡ 3 mod 8` and `d ≡ 7 mod 16`, that `Real.log q` is strictly above `Y^(ε/5)/2` and at most `Y^(ε/5)`, that `Real.log d` is strictly above `Y^(ε/5)·(log Y)²/2` and at most `Y^(ε/5)·(log Y)²`, and that `q` and every odd prime up to `Y^(ε/5)` divide `d + 1`, with no mention of a host in `WinPair` itself.

### Row 3.3 (differs)

Lean source checked in `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` line 143, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean` lines 26-28, lines 92-96, line 138, and lines 146-148, `src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean` lines 17-27, `src/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean` lines 42-54.

```lean
  bdG : H.BoundedCharsPointwise Λ.KEPT x eps

def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then ((G y : ℝ) : ℂ) else sumLamChi χ y + (y : ℂ) * logDerivativeAtOne χ

def TrivialOnFirstFactor {φ : Frame} (θ : φ.Char) : Prop := ∀ s ∈ φ.A0, θ (φ.tau1 s) = 1

def Xp : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = 1}

def Xm : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = -1}

def Bounded (S : Finset PChar) : Set φ.Char := {θ | (θ ∈ φ.Xp ∧ ¬ H.Kept S θ) ∨ θ ∈ φ.Xm}

def BoundedCharsPointwise (S : Finset PChar) (x eps : ℝ) : Prop :=
  ∀ θ ∈ H.Bounded S, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps)

theorem UpperTheory.T3.supplyOfAdmOf :
    (∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C0 → ∃ CT2 C8 c6 Cb x0 : ℝ, C0 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧
      ∀ (s : Scale) (R : Ranks) (H0 : HostAx R.toFrame) (M : ℕ) (Y : ℝ), s.eps = eps → x0 ≤ s.x → RankVal s R →
        s.J ≤ C0 → (R.o : ℝ) ≤ C0 → (H0.QS : ℝ) ≤ C0 * R.n → 0 < M → (M : ℝ) ≤ C0 → H0.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M →
        PairWin s Y → PairGood M eps Y s.x H0.q H0.d → FieldRows H0.toHostRaw ⌊Y ^ (eps / 5)⌋₊ → admitted R H0 →
        ∃ (H : Host R) (q0 : ℕ), H.toHostAx = H0 ∧ H.CT2 = CT2 ∧ HostGood s C8 4 c6 Cb H q0 ∧
          R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps))) → ∀ ψ : PChar, VWinAt ψ 401 →
      (∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (φ : Frame) (H0 : HostAx φ), s.eps = eps → x0 ≤ s.x →
        s.x ^ (2 + 8 * eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * eps) → φ.o = (Level.cyc ψ).o → KerChi ψ H0.toHostRaw →
        ∃ (R : Ranks) (h : R.toFrame = φ), RankVal s R ∧ admitted R (h ▸ H0)) →
      HostExW (3 / 2) (fun _ s R H _ => EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (Real.sqrt s.b)) := by

theorem UpperTheory.Comparison₂.sigA_le :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), 0 < x →
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell →
        SigA (arith H.toHostRaw) ell φ.A0 (keptA Λ H.toHostRaw) x ≤ 4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by

    exact hE.bdG _ (chr_bounded Λ φ H.toHostRaw ψ hψ.1 hψ.2) _ _ (HostRaw.isPrimOf_prim _ _)
```

First, `Bounded` is defined as the union of `{θ ∈ φ.Xp | ¬ H.Kept S θ}` and `φ.Xm`, so the `φ.Xm` branch does not require `¬ H.Kept S θ` in the definition itself (as an interpretation, `EAtH.kept` together with `HostAx` places kept characters in `φ.Xp`). Second, `bdG` bounds `‖An.gChi χ x‖`, which for `χ ≠ 1` includes `(x : ℂ) * logDerivativeAtOne χ` alongside `sumLamChi χ x` (and equals `G x` for `χ = 1`), rather than purely a prime sum. Third, the named declarations do not state that one theorem fills `bdG` and one uses it, since `supplyOfAdmOf` proves `HostExW (3/2)` containing `EAtH (Level.cyc ψ) ... 4` only conditionally from three hypotheses and only for `Level.cyc ψ` (and `supplyOfAdm` and `supplyChi` share that conclusion via `supplyOfAdmOf`), while `sigA_le` uses `hE.bdG` in its proof.

Corrected row text replaces the table summary with the statement below.

> The set `Bounded` consists of host characters trivial on `φ.A0` that either lie in `φ.Xp` and are not kept or lie in `φ.Xm`, and `bdG` requires each primitive character `χ` induced by one of them to satisfy `‖An.gChi χ x‖ ≤ x^(1/2 + ε)`. Under three hypotheses on host construction, `VWinAt ψ 401`, and `admitted` ranks, `supplyOfAdmOf` constructs `EAtH` for `Level.cyc ψ` with constant `4`, and `sigA_le` uses `bdG` to bound `SigA` by `4·Λ.o·x^(1/2 + ε)`.

### Row 3.4 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairShare.lean` lines 30-35, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean` lines 13-16, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean` lines 22-27 and lines 32-34, `src/Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean` lines 49-53.

```lean
theorem pair_share :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K η : ℝ) (N₀ : ℕ), 0 < ε → ε < 1 / 52 → 0 < τ → 1 ≤ K → 0 < η → 0 < N₀ → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ X z' : ℝ, X ≤ Y ^ K → Y ^ (ε / 5) * Real.log Y ^ 2 ≤ z' → z' ≤ K ^ 2 * (Y ^ (ε / 5) * Real.log Y ^ 2) →
      ∃ G₁ ⊆ primePairSetFirst (Y ^ (ε / 5)), 0 < (primePairSetFirst (Y ^ (ε / 5))).card ∧ (1 - η) * (primePairSetFirst (Y ^ (ε / 5))).card ≤ G₁.card ∧ ∀ q ∈ G₁,
        GoodQ N₀ C τ Y X (Y ^ (ε / 5)) q ∧ ∃ G₂ ⊆ primeSetTwoBounds (Y ^ (ε / 5)) z' q, 0 < (primeSetTwoBounds (Y ^ (ε / 5)) z' q).card ∧
          (1 - η) * (primeSetTwoBounds (Y ^ (ε / 5)) z' q).card ≤ G₂.card ∧ ∀ d ∈ G₂, GoodD N₀ C τ Y X (Y ^ (ε / 5)) z' q d := by

theorem pair_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K : ℝ) (N₀ : ℕ), 0 < ε → ε < 1 / 52 → 0 < τ → 1 ≤ K → 0 < N₀ → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ X z' : ℝ, X ≤ Y ^ K → Y ^ (ε / 5) * Real.log Y ^ 2 ≤ z' → z' ≤ K ^ 2 * (Y ^ (ε / 5) * Real.log Y ^ 2) →
      ∃ q d : ℕ, Rows (Y ^ (ε / 5)) z' q d ∧ N₀ < q ∧ GoodQ N₀ C τ Y X (Y ^ (ε / 5)) q ∧ GoodD N₀ C τ Y X (Y ^ (ε / 5)) z' q d := by

structure PairGood (M : ℕ) (eps Y X : ℝ) (q d : ℕ) : Prop where
  pair : WinPair eps Y q d
  coprime : Nat.Coprime M (q * d)
  bounds : ∀ (ξ : DirichletCharacter ℂ M) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw (fun a => ξ (a : ZMod M)) q d i j) (2 * M * q * d) →
      ∀ y : ℝ, Y ≤ y → y ≤ X → ‖An.gChi χ y‖ ≤ y ^ ((1 : ℝ) / 2 + eps / 2) ∧ ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log y

def PairEx : Prop :=
  ∀ (M : ℕ), 0 < M → ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ A →
    ∃ Y1 : ℝ, ∀ Y ≥ Y1, ∃ q d : ℕ, PairGood M eps Y (Y ^ A) q d

theorem UpperTheory.Top.boundedTw :
    ∀ (ψ : PChar) (φ : Frame) (H : HostRaw φ) (eps Y x : ℝ), 0 < eps → 1 ≤ x → Y ≤ x → TwistForm ψ H → ψ.N ∣ H.QS →
      (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * ψ.N) → PairGood ψ.N eps Y x H.q H.d →
      H.BoundedCharsPointwise (Level.cyc ψ).KEPT x eps ∧
        ∀ θ ∈ H.Bounded (Level.cyc ψ).KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ → ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log x := by
```

First, `pair_share`, `pair_exists`, and `PairEx` (`pairEx`) all require `0 < ε` and `ε < 1 / 52` (as well as positive `N₀` or `M`), which the row omits. Second, `pair_share` proves `GoodQ` and `GoodD` (`Box` on twists of characters of modulus `N₀` for arbitrary `τ > 0` and share `1 − η`), `pair_exists` specializes `η = 1/2` to choose one pair, and `pairEx` produces `PairGood M ε Y (Y^A) q d` for twists of `DirichletCharacter ℂ M`, rather than directly for the host set `H.Bounded`. Third, `boundedTw` connects `PairGood` to `H.Bounded (Level.cyc ψ).KEPT` only for `Level.cyc ψ`, only under `TwistForm ψ H`, `ψ.N ∣ H.QS`, and prime factors of `H.QS` dividing `2·ψ.N`, and only at the single point `x` with exponent `1/2 + ε` rather than `y^(1/2 + ε/2)` across `[Y, Y^A]`. Also `An.gChi χ y` includes `(y : ℂ) * logDerivativeAtOne χ` for nontrivial `χ`.

Corrected row text replaces the table summary with the statement below.

> For `0 < ε < 1/52`, `A ≥ 1`, `M > 0`, and every large `Y`, `pair_share` gives at least a `1 − η` share of candidate primes `q` and then `d` satisfying `GoodQ` and `GoodD`, `pair_exists` sets `η = 1/2` to pick one pair, and `pairEx` yields `PairGood M ε Y (Y^A) q d` bounding `‖An.gChi χ y‖ ≤ y^(1/2 + ε/2)` and `‖An.logDerivativeAtOne χ‖ ≤ 4·log y` for twists of characters mod `M` over `y` from `Y` to `Y^A`. For `Level.cyc ψ` under `TwistForm ψ H` and the divisibility hypotheses on `H.QS`, `boundedTw` turns `PairGood` at `x ≥ Y` into the bound `x^(1/2 + ε)` on `H.Bounded`.

### Row 3.5 (says more)

Lean source checked in `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean` lines 45-51 and lines 104-108, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean` lines 17-18 and lines 36-40, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean` lines 37-40.

```lean
theorem stage :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K η : ℝ) (R : ℕ), 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K → 0 < η → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ (U F : ℝ) (m₀ a₀ : ℕ) (Ξ : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), admitted ε Y U m₀ a₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ Y ^ (ε / 5) ∨ (Y ^ K) ^ 400 < (p : ℝ)) →
      1 ≤ F → F ≤ U ^ (1 / 2 : ℝ) → Ξ.card ≤ R → (∀ ξ ∈ Ξ, ξ.2.IsPrimitive ∧ ((ξ.1 + 1 : ℕ) : ℝ) ≤ F) →
      (PPset m₀ a₀ U).Nonempty ∧ ∀ B ⊆ PPset m₀ a₀ U,
        (∀ q ∈ B, ∃ ξ ∈ Ξ, ∃ M : ℕ, M ≠ 0 ∧ ¬ BoxAll (F * U) C τ Y (Y ^ K) (fun n => ξ.2 n * J q n) M) →
        (B.card : ℝ) ≤ η * (PPset m₀ a₀ U).card := by

  set B₁ := B.filter (fun q => ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
    (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ F * U ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox (F * U) ψ) with hB₁
  set B₂ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → Finset ℕ := fun ξ => B.filter (fun q =>
    ∃ y ∈ Set.Icc Y (Y ^ K), y ^ (1 / 2 + τ) / 2 < ‖S ((Y ^ K) ^ 400) y q (fun n => ξ.2 n)‖) with hB₂
  have hsub : B ⊆ B₁ ∪ Ξ.biUnion B₂ := by

def S (Z y : ℝ) (q : ℕ) (κ : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊Z⌋₊, ((cN y n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)

def GoodC (Q : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : Prop :=
  ψ ≠ 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q ψ

def Box (Q C τ Y X : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : Prop :=
  GoodC Q ψ ∧ ‖logDerivLAtOne ψ‖ ≤ C * Real.log Y ∧ ∀ y ∈ Set.Icc Y X, ‖Gchi ψ y‖ ≤ y ^ (1 / 2 + τ)

theorem box_of_S :
    ∃ C : ℝ, 0 < C ∧ ∀ ε τ K : ℝ, 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (q : ℕ) (κ : ℕ → ℂ),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ → (∀ n : ℕ, χ (n : ZMod N) = κ n * J q n) →
      (∀ y ∈ Set.Icc Y (Y ^ K), ‖S ((Y ^ K) ^ 400) y q κ‖ ≤ y ^ (1 / 2 + τ) / 2) → Box Q C τ Y (Y ^ K) χ := by
```

The row omits the hypotheses under which `stage` and `box_of_S` reduce failing `Box` to the two failure sets `B₁` and `B₂`, namely `0 < ε ≤ 1 / 4`, `0 < τ`, `1 ≤ K`, `0 < η`, `Y ≥ Y₀`, `admitted ε Y U m₀ a₀`, the prime-divisor condition on `m₀`, `1 ≤ F ≤ U^(1/2)`, `Ξ.card ≤ R`, primitive characters `ξ ∈ Ξ` of modulus at most `F`, and `Y^(ε/6) ≤ Real.log Q ≤ Y^(ε/4)` in `box_of_S`. Also, `Box` itself has a second condition `‖logDerivLAtOne ψ‖ ≤ C * Real.log Y`, `B₁` checks `ZeroFreeBox (F * U)` for primitive characters of modulus `f * q ≤ F * U` with `f ≤ F`, and `S` sums over prime powers up to `⌊(Y^K)^400⌋₊` with weights `Λ(n)·min(1, y/n)`.

Corrected row text replaces the table summary with the statement below.

> Under the hypotheses of `stage` (including `0 < ε ≤ 1/4`, `Y ≥ Y₀`, `admitted`, `1 ≤ F ≤ √U`, and primitive base characters `ξ ∈ Ξ` of modulus at most `F`), any candidate prime `q` failing `BoxAll` falls into `B₁` or `B₂` via `box_of_S`. Either a primitive character of modulus `f·q ≤ F·U` with `f ≤ F` has an L-function zero with real part above `1 − 1/400` and imaginary part at most `F·U` in absolute value, or for some `ξ ∈ Ξ` and `y` in `[Y, Y^K]` the truncated prime-power sum `S` up to `(Y^K)^400` exceeds `y^(1/2 + τ)/2` in absolute value.

### Row 3.6 (says more)

Lean source checked in `src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean` lines 13-16, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean` lines 11-15, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean` lines 350-354, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean` lines 22-28.

```lean
theorem count_bad :
    ∃ C : ℝ, ∀ (Q F : ℝ) (B : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ B, q.Prime ∧ F < q ∧ ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox Q ψ) → (B.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by

def ZeroDensityBox : Prop :=
  ∃ C : ℝ, ∀ (Q : ℝ) (S : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), 3 ≤ Q →
    (∀ p ∈ S, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

theorem count_a (hP : PNTAPRelW) (hE : Formalism.ZeroFreeDirichlet.ExcBound) (ε : ℝ) (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ (x X : ℝ) (m₀ a₀ : ℕ),
    x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by

structure admitted (ε Y U : ℝ) (m₀ a₀ : ℕ) : Prop where
  pos : 0 < m₀
  eight : 8 ∣ m₀
  coprime : a₀.Coprime m₀
  log_m : (1 / 4) * Real.log Y ^ 2 * Real.log m₀ ≤ Real.log U
  lo : Y ^ (ε / 6) ≤ Real.log U
  hi : Real.log U ≤ Y ^ (ε / 5) * Real.log Y ^ 2
```

First, both `zero_density_box` (`ZeroDensityBox`) and `count_bad` require `3 ≤ Q` (and `count_bad` also requires `F < q`, `f ≤ F`, and `f * q ≤ Q`), which the row omits. Second, `count_a` requires `PNTAPRelW`, `ExcBound`, `0 < ε`, and `x₀ ≤ Y` (sufficiently large `Y`) in addition to the six fields of `admitted ε Y U m₀ a₀`. As an interpretation, without large `Y`, `admitted` alone can hold for small `Y` and `U < 2` where `PPset` is empty.

Corrected row text replaces the table summary with the statement below.

> For `Q ≥ 3`, `zero_density_box` bounds the number of primitive characters of modulus at most `Q` with a zero of the kind of 3.5 by a constant times `Q^(1/4)`, and `count_bad` transfers this bound to primes `q > F` with `f·q ≤ Q` and `f ≤ F`. Under `PNTAPRelW`, `ExcBound`, `0 < ε`, and `admitted`, `count_a` states that for every sufficiently large `Y` the set `PPset m₀ a₀ U` holds at least `U^(9/10)` primes.

### Row 3.7 (says more)

Lean source checked in `src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean` lines 55-58, `src/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean` lines 12-18, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean` lines 255-258, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean` lines 30-31.

```lean
theorem meanSqK :
    ∃ C : ℝ, 0 < C ∧ ∀ ε K : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m₀ a₀ : ℕ),
      admitted ε Y U m₀ a₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ Y ^ (ε / 5) ∨ (Y ^ K) ^ 400 < (p : ℝ)) →
      MeanSq C ((Y ^ K) ^ 400) (PPset m₀ a₀ U) (Set.Icc Y (Y ^ K)) := by

theorem meanSq_abs :
    ∀ (P : Finset ℕ) (m₀ a₀ nstar : ℕ) (Z y η B : ℝ) (κ : ℕ → ℂ), 8 ∣ m₀ → a₀.Coprime m₀ → 0 ≤ y → 0 ≤ η →
      (∀ q ∈ P, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ ⌊Z⌋₊ ^ 2 < q) → (∀ n, ‖κ n‖ ≤ 1) → (∀ p, sP (cN y) ⌊Z⌋₊ p ≤ B) →
      (∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊Z⌋₊ ^ 2 → s ≠ nstar →
        |∑ q ∈ P, (jacobiSym (q : ℤ) s : ℝ)| ≤ η * P.card) →
      ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤ ((∑ p ∈ (Icc 1 ⌊Z⌋₊).filter Nat.Prime, sP (cN y) ⌊Z⌋₊ p ^ 2) + RR (cN y) m₀ ⌊Z⌋₊ ^ 2 +
        (2 * B ^ 2 + 2 * B * RR (cN y) m₀ ⌊Z⌋₊) + η * (∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n) ^ 2) * P.card := by

theorem bad_share :
    ∀ C τ η : ℝ, 0 ≤ C → 0 < τ → 0 < η → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (X Z : ℝ) (P B : Finset ℕ) (κ : ℕ → ℂ),
      (∀ n, ‖κ n‖ ≤ 1) → MeanSq C Z P (Set.Icc Y X) → B ⊆ P →
      (∀ q ∈ B, ∃ y ∈ Set.Icc Y X, y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖) → (B.card : ℝ) ≤ η * P.card := by

def MeanSq (C Z : ℝ) (P : Finset ℕ) (A : Set ℝ) : Prop :=
  ∀ y ∈ A, ∀ κ : ℕ → ℂ, (∀ n, ‖κ n‖ ≤ 1) → ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤ C * y * Real.log y * P.card
```

`meanSqK` proves the `MeanSq` bound only under `0 < ε ≤ 1`, `1 ≤ K`, sufficiently large `Y ≥ Y₀`, `admitted ε Y U m₀ a₀`, the prime-divisor hypothesis on `m₀`, `y ∈ Set.Icc Y (Y ^ K)`, and `‖κ n‖ ≤ 1`, while `meanSq_abs` assumes `8 ∣ m₀`, `a₀.Coprime m₀`, `⌊Z⌋₊^2 < q`, and the character-sum cancellation hypothesis. Likewise, `bad_share` proves `(B.card : ℝ) ≤ η · P.card` for `C ≥ 0`, `τ > 0`, and `η > 0` only for sufficiently large `Y ≥ Y₀`. The row omits these hypotheses on `ε`, `K`, `Y`, `admitted`, `m₀`, and the interval of `y`.

Corrected row text replaces the table summary with the statement below.

> For `0 < ε ≤ 1`, `1 ≤ K`, large `Y`, `admitted ε Y U m₀ a₀`, and prime factors of `m₀` at most `Y^(ε/5)` or above `(Y^K)^400`, `meanSqK` (using `meanSq_abs`) proves that for every `y` in `[Y, Y^K]` and `‖κ n‖ ≤ 1` the sum of `‖S‖²` over `PPset m₀ a₀ U` is at most a constant times `y·log y` times the number of primes. Given `MeanSq` on `[Y, X]`, `τ > 0`, and `η > 0`, `bad_share` proves for every large `Y` that the subset where `‖S‖ > y^(1/2 + τ)/2` for some `y` in `[Y, X]` has size at most `η` times the set size.

### Row 3.8 (differs)

Lean source checked in `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean` lines 47-50, `src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean` lines 158-161.

```lean
theorem abs_pair_sum_eq (PP : Finset ℕ) (m₀ a₀ n n' : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hn : 0 < n)
    (hn' : 0 < n') (hPP : ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q) :
    |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by

theorem twistK :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m₀ a₀ : ℕ), admitted ε Y U m₀ a₀ →
      ∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → (s : ℝ) ≤ Y ^ A → s ≠ nstar →
        |∑ q ∈ PPset m₀ a₀ U, (jacobiSym (q : ℤ) s : ℝ)| ≤ Y ^ (-B) * ((PPset m₀ a₀ U).card : ℝ) := by
```

First, `abs_pair_sum_eq` requires `8 ∣ m₀`, `a₀.Coprime m₀`, `0 < n`, `0 < n'`, and `n · n' < q` for every `q ∈ PP`, and its statement equates the absolute values `|∑ (n/q)·(n'/q)|` and `|∑ (q / soutPart m₀ (n·n'))|` (where `soutPart m₀ (n·n')` can be `1`, giving `(q/1) = 1`, and the statement itself does not name `(p/r)` as a real character of `p`). Second, `twistK` requires `0 < ε`, `0 < A`, `0 < B`, sufficiently large `Y ≥ Y₀`, and `admitted ε Y U m₀ a₀`, which the row omits, and its conclusion bounds the absolute value `|∑ q ∈ PPset m₀ a₀ U, (jacobiSym (q : ℤ) s : ℝ)|` rather than only the signed sum without absolute values.

Corrected row text replaces the table summary with the statement below.

> When `8 ∣ m₀`, `a₀` is coprime to `m₀`, `n` and `n'` are positive, and `n·n' < p` for every prime `p` of the set in residue class `a₀ mod m₀`, `abs_pair_sum_eq` states that `|∑ (n/p)·(n'/p)|` equals `|∑ (p/r)|` with `r = soutPart m₀ (n·n')`. For `0 < ε`, `0 < A'`, `0 < B'`, sufficiently large `Y`, and `admitted ε Y U m₀ a₀`, `twistK` bounds `|∑ (p/r)|` over `PPset m₀ a₀ U` by `Y^(−B')` times the number of primes for every odd squarefree `r > 1` coprime to `m₀` and at most `Y^A'`, with at most one exception.

### Row 4.1 (differs)

Lean source checked in `src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean` lines 76-95 and `src/Formalism/ThickAverageLoss/PartnersToFactorsAt.lean` lines 25-34.

```lean
def IsInert (D : ArithData H) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p ≠ D.q1 ∧ p ≠ D.d ∧ ¬ InPhi (D.frob p)

def askP (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ (Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p)),
    max (a / (p : ℝ) ^ i - w (partner t (i • D.frob p))) 0

def askD (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ := by
  classical
  exact ∑ i ∈ Icc 1 N, ∑ g ∈ univ.filter (fun g => g - i • D.frob D.d ∈ D.inertia D.d ∧ ¬ InPhi g),
    max (a / (D.d : ℝ) ^ i - w (partner t g)) 0

def ASK (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ := by
  classical
  exact (∑ p ∈ (range (N + 1)).filter (IsInert D), 2 * Real.log p * askP D N a t w p)
    + Real.log D.d * askD D N a t w

def MAIN (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (w : E0 × H → ℝ) : ℂ :=
  (a : ℂ) * (((Real.log a - 1 - Real.eulerMascheroniConstant : ℝ) : ℂ) + ell chC
    - (((1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ))
```

`ASK` differs from the row in three ways. First, `IsInert D p` requires `p ≠ 2`, `p ≠ D.q1`, and `p ≠ D.d` in addition to `p.Prime` and `¬ InPhi (D.frob p)`, and the sum runs over `p ∈ range (N + 1)` (so `p ≤ N`). Second, `askP` sums over `i ∈ Icc 1 N` with `¬ InPhi (i • D.frob p)` and weights `max (a / p ^ i - w (partner t (i • D.frob p))) 0`, so `ASK` includes prime powers `p ^ i` and `D.d` is not assumed prime inside `ASK`. Third, `MAIN` takes `a` as a direct real argument rather than from a record, and is an exact complex formula containing `ell chC`, `- 1 - γ`, and the average of `Real.log (w ρ)` over `PhiSet`, with no order statement of `a · log a`.

Corrected row text replaces the table summary with the statement below.

> `ASK` sums `2 * Real.log p * askP D N a t w p` over primes `p ≤ N` satisfying `IsInert D p` (namely `p ≠ 2`, `p ≠ D.q1`, `p ≠ D.d`, and `¬ InPhi (D.frob p)`), where `askP` sums `max (a / p ^ i - w (partner t (i • D.frob p))) 0` over powers `i ∈ Icc 1 N` with `¬ InPhi (i • D.frob p)`, plus `Real.log D.d * askD D N a t w` for the parameter `D.d`. `MAIN ell a w` is the complex expression `(a : ℂ) * ((Real.log a - 1 - γ) + ell chC - (1 / |PhiSet|) * ∑ ρ ∈ PhiSet, Real.log (w ρ))`, taking a real parameter `a` rather than a field of a record.

### Row 4.2 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean` lines 204-206 and `src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean` lines 72-74, 97-100.

```lean
def GPsi (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (y : ℝ) : ℂ :=
  if ψ = 0 then ((Gz y : ℝ) : ℂ) else
    (∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℂ) * primVal D ψ n * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * ell ψ

def De (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
    ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ((w (partner t g) : ℝ) : ℂ)
      * GPsi D ell ψ (a / w (partner t g))

theorem ch_balance {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ) (hD : HostFactsS D S)
    (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (ha : 0 < a) (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) : (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w
```

The row omits the four hypotheses of `ch_balance` (`HostFactsS D S`, `0 < a`, `∀ ρ, InPhi ρ → 0 < w ρ`, and `∀ ρ, InPhi ρ → a / w ρ ≤ N`) and the complex cast on `ASK`. Furthermore, `De` is not a bare average of prime sums over characters because `De` scales by `1 / (PhiSet.card : ℂ)` while summing over both `¬ InPhi g` and all `ψ`, weights each term by `starRingEnd ℂ (ψ g) * w (partner t g)`, and uses `GPsi`, which sums over prime powers via `vonMangoldt` and adds `y * ell ψ` for `ψ ≠ 0` or equals `Gz y` for `ψ = 0`.

Corrected row text replaces the table summary with the statement below.

> Under `HostFactsS D S`, `0 < a`, `∀ ρ, InPhi ρ → 0 < w ρ`, and `∀ ρ, InPhi ρ → a / w ρ ≤ N`, `(ASK D N a t w : ℂ) - MAIN ell a w` equals `De D ell a t w`, which scales by `1 / (PhiSet.card : ℂ)` the double sum over `¬ InPhi g` and characters `ψ` of `E0 × H` of `starRingEnd ℂ (ψ g) * w (partner t g) * GPsi D ell ψ (a / w (partner t g))`.

### Row 4.3 (says less)

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` lines 32-77, 287-343.

```lean
lemma core (A0 : AddSubgroup H) (D : ArithData H) (S : Finset ℕ) (hD : HostFactsS D S) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ}
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) {x b b' η X' θ Err Y : ℝ}
    (hx : 3 ≤ x) (hb : 0 < b) (hS : SizesA A0 TT T2 a w N x b b' η X' θ) (hThin : ThinScales D ell X' θ)
    (hC : CostWindows x (fPl H) b η θ) (hT2 : ∀ s ∈ T2, s ∈ A0)
    (hTop : ∀ u0 ∈ A0, gapA D N ell TT a w u0 ≤ Err)
    (hY : (TT.card : ℝ) * Y ≤ ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ (a t / b)).re) :
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * Y ≤ Err + 2 * (TT.card : ℝ) * m * b / x
```

Row 4.3 describes two steps inside the proof of `core` (`sum_A` and `sum_Th` filtering characters to `PsiA A0`, and the `Fin m` sum multiplying `(Th D ell T2 b (a t / b) u t).re` by `m`) while omitting the hypotheses and inequality conclusion of `core` itself, as well as the `s ↦ (0, s)` embedding of `A0` into `E0 × H`.

Corrected row text replaces the table summary with the statement below.

> Assuming `3 ≤ x`, `0 < b`, `SizesA`, `ThinScales`, `CostWindows`, `T2 ⊆ A0`, `gapA ≤ Err` on `A0`, and the lower bound on `Y` from `PsiA A0`, `core` concludes `(TT.card : ℝ) * m * b * (delta2 T2 / 2) * Y ≤ Err + 2 * (TT.card : ℝ) * m * b / x`. In its proof, summing `Th` over `A0` removes every character nontrivial on `{(0, s) | s ∈ A0}`, and the sum over `Fin m` multiplies the lift-independent term `(Th ...).re` by `m`.

### Row 4.4 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` lines 347-355 and `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean` lines 38-44, 54-56.

```lean
def GmA (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Kp : Finset (AddChar (E0 × H) ℂ)) (c y : ℝ) : ℝ :=
  ∑ ψ ∈ Kp, wtA c ψ * (GPsi D ell ψ y).re

def SigA (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (y : ℝ) : ℝ :=
  ∑ ψ ∈ PsiA A0 \ Kp, ‖GPsi D ell ψ y‖

theorem ch_core (C ε CE Ko c M : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hc : |c| ≤ 1) : ∃ x1 : ℝ, ∀ x ≥ x1,
    ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (m : ℕ) (D : ArithData H) (S : Finset ℕ)
      (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
      (b b' k aE η X' θ : ℝ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)),
      HostFactsS D S → 0 < b → 0 ≤ aE → 0 < k → (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) → x * m ≤ k →
      SizesA A0 TT T2 a w N x b b' η X' θ → ThinScales D ell X' θ → CostWindows x (fPl H) b η θ →
      RestSize ε x (Fintype.card H) TT.card T2.card m b k aE → (∀ s ∈ T2, s ∈ A0) → CharsA ell A0 Kp TT c M Ko CE ε x →
      (∀ u ∈ A0, gapA D N ell TT a w u ≤ x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card H) TT.card T2.card m b k aE) →
      GmA D ell Kp c x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) + SigA D ell A0 Kp x
```

Row 4.4 omits the threshold `∃ x1, ∀ x ≥ x1` and twelve hypotheses required by `ch_core` in addition to the `gapA` bound (which uses the real part of `MAIN` and holds for every `u ∈ A0`). It also misstates both sides of the conclusion, since `GmA` is the sum over `Kp` of `wtA c ψ * (GPsi D ell ψ x).re` (weighted by `1` or `c` and including `ell ψ` or `Gz`, not a bare prime sum), and `SigA` sums `‖GPsi D ell ψ x‖` only over `PsiA A0 \ Kp`, not over all other characters of `E0 × H`.

Corrected row text replaces the table summary with the statement below.

> Given `0 ≤ C`, `0 < ε`, and `|c| ≤ 1`, there exists `x1` such that for all `x ≥ x1` and under `HostFactsS`, `0 < b`, `0 ≤ aE`, `0 < k`, `m ≤ x^(1/2 + ε/2)`, `x * m ≤ k`, `SizesA`, `ThinScales`, `CostWindows`, `RestSize`, `T2 ⊆ A0`, `CharsA`, and `gapA ≤ x^(Cε) * errorBracketSizeWindows` for every `u ∈ A0`, `ch_core` concludes `GmA D ell Kp c x ≤ x^(1/2 + (C + 3)ε) + SigA D ell A0 Kp x`.

### Row 5.1 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean` lines 41-48 and `src/Formalism/SizeWindowBrackets/SChain.lean` lines 21-23 and `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 39-78.

```lean
def SizeData₂ (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : Prop :=
  Dd.HidaSetting C ∧ Dd.DIV C ∧ EComp5 Dd C ∧ Dd.HComp C ∧ Count5 Dd C ∧ Dd.Slopes C ∧
  QuotientSlopeBoundsWith Dd C Xpp ∧ LossBounds Dd C ∧ Dd.SlopeIneq ∧ Dd.HHBound C ∧ Dd.FParams

theorem ch_top {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H))
    (h1 : IdentU Dd tr D N ell TT a w eT eP) (h2 : SizeData₂ Dd C Xpp) (h3 : ErrWindows Dd C Xpp eK K) (h4 : BNBoundsU Dd T2)
    (h5 : LargeX Dd.x Dd.ε K C.cHH eK) (u : U0) :
    gapA D N ell TT a w (tr u) ≤
      Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a
```

`ch_top` does not follow from the eleven conditions `SizeData₂` alone, because it also requires `IdentU`, `ErrWindows`, `BNBoundsU`, and `LargeX` (and takes `C` of type `Consts` and `Xpp` of type `ℝ`). Moreover, `Data` holds both real numbers and real-valued functions indexed by `U0`, `W u0`, `Top`, `Fin m`, and `Fin f`, and `ch_top` bounds `gapA` (the sum of `ASK - (MAIN ...).re` over `TT` and `Fin m`).

Corrected row text replaces the table summary with the statement below.

> Under `IdentU`, the eleven conditions `SizeData₂`, `ErrWindows`, `BNBoundsU`, and `LargeX` on a record `Data` of real numbers and real-valued functions (together with `C` and `Xpp`), `ch_top` proves the `gapA` bound `gapA D N ell TT a w (tr u) ≤ Dd.x^(CErr C * Dd.ε) * errorBracketSizeWindows ...`.

### Row 5.2 (says less)

Lean source checked in `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 13-13, 90-90, 116-119.

```lean
def DIV : Prop :=
  ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u)))
      + C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
```

`DIV` quantifies over both `u0` in `U0` and `u` in `W u0` (with `muCC` and `Fo` depending on `u0`, and `h` and `T` depending on `u0` and `u`), whereas Row 5.2 omits `u0`. It also leaves `Fo` and the explicit error terms `C.cDiv * D.nT * D.a * D.La + C.cDiv * m * (D.B0 + D.Nc) * D.x^(C.eDiv * D.ε)` unnamed, and calls `Top` top places and `D.logOm` the constant of 7.4 even though `Data` uses an abstract finite type `Top` and abstract fields `D.gam`, `D.v`, and `D.LpL`.

Corrected row text replaces the table summary with the statement below.

> The condition `DIV` says for every `u0` in `U0` and every `u` in `W u0` that `D.muCC u0 + D.h u0 u - D.Fo u0` is at most the sum over `t` in `Top` of `m * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u)` plus `C.cDiv * D.nT * D.a * D.La + C.cDiv * m * (D.B0 + D.Nc) * D.x^(C.eDiv * D.ε)`.

### Row 5.3 (says less)

Lean source checked in `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 15-15, 94-97, 130-138.

```lean
def SlopeIneq : Prop :=
  ∀ u0, 0 ≤ D.del u0 → D.del u0 < 1 → 0 ≤ D.η u0 → 0 ≤ D.e u0 → D.e u0 ≤ 1 / 4 →
    D.s u0 - D.muMinCC u0 ≤ D.HH u0 → 0 < D.HH u0 →
    D.s u0 - Real.log (Fintype.card (W u0) : ℝ)
      - (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤ D.muCC u0

def HHBound : Prop :=
  ∀ u0, D.s u0 - D.muMinCC u0 ≤ D.HH u0 ∧ 0 < D.HH u0 ∧ D.HH u0 ≤ D.x ^ C.cHH * D.b
```

Row 5.3 omits the outer quantification over `u0`, the weights `D.d u0`, the explicit correction formula, the exact ranges (`0 ≤ D.del u0 < 1`, `0 ≤ D.η u0` with no upper bound in `SlopeIneq`, and `0 ≤ D.e u0 ≤ 1 / 4`), and the third conjunct `D.HH u0 ≤ D.x ^ C.cHH * D.b` of `HHBound`.

Corrected row text replaces the table summary with the statement below.

> The condition `SlopeIneq` says for every `u0` in `U0` that when `0 ≤ D.del u0 < 1`, `0 ≤ D.η u0`, `0 ≤ D.e u0 ≤ 1/4`, and `0 < D.HH u0` with `D.s u0 - D.muMinCC u0 ≤ D.HH u0`, the `D.d u0`-weighted mean `D.s u0` of `D.muN u0 u - D.h u0 u` minus `Real.log (Fintype.card (W u0))` and minus `(1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0)` is at most `D.muCC u0`. `HHBound` supplies the two inequalities on `D.HH u0` together with `D.HH u0 ≤ D.x^C.cHH * D.b`.

### Row 5.4 (differs)

Lean source checked in `src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean` lines 60-63 and `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean` lines 46-62, 109-156, 171-193.

```lean
def PointwiseBoundVariant : Prop :=
  D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0

lemma s_lower5 (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.Ga u0 + D.muCC u0 - K5v5 D C u0 - wmean (D.d u0) (Lo5 D C Xpp u0) ≤ D.s u0

theorem each_unit_bound_statement {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : PointwiseBoundVariant D C Xpp
```

The statement of `each_unit_bound_statement` is `PointwiseBoundVariant D C Xpp`, which assumes all eleven conditions of `SizeData₂` (not only `DIV` and `SlopeIneq`) and concludes `∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0`, without mentioning a weighted mean of `muN`. Moreover, in the proof (`s_lower5` and `Ga_bound5`), Lean never separates out the weighted mean of `muN` alone, and instead `s_lower5` uses `DIV` and `QuotientSlopeBoundsWith` to bound `D.s u0` (the weighted mean of `muN - h`) from below, and `Ga_bound5` combines that lower bound on `D.s u0` with the upper bound from `SlopeIneq` to cancel `D.s u0` and `D.muCC u0` and bound `D.Ga u0`.

Corrected row text replaces the table summary with the statement below.

> The theorem `each_unit_bound_statement` takes all eleven conditions of `SizeData₂` and concludes `∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0`. In its proof, `s_lower5` combines `DIV`, `QuotientSlopeBoundsWith`, `Count5`, `EComp5`, `Slopes`, and `HidaSetting` to bound `D.s u0` (the weighted mean of `muN - h`) from below, `Ga_bound5` pairs that with `SlopeIneq` to cancel `D.s u0` and `D.muCC u0` and bound `D.Ga u0` from above, and `LossBounds` bounds `D.ASK u0` through `D.Ga u0`.

### Row 5.5 (differs)

Lean source checked in `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 56-56, 105-111 and `src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean` lines 31-36.

```lean
def Main (u0 : U0) : ℝ :=
  ∑ j : Fin m, ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL
    - (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))

def Count5 : Prop :=
  ∀ u0 (u : W u0),
    ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
        - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k) ≤ Real.log (D.T u0 u)) ∧
    Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k
```

First, `w` and `T` and `Main` depend on `u0` in `U0`, and positivity `0 < D.w u0 j ρ` is a conjunct of `HidaSetting`, not `Data`. Second, `Count5` contains three inequalities (a lower bound, an upper bound `Real.log (D.T u0 u) ≤ C.cCount * m * D.L`, and a comparison `|Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k`), of which Row 5.5 states only the first. Third, `Data.Main` uses the abstract real fields `D.gam` and `D.LpL` of `Data`, not `γ` and the logarithmic derivative of 7.4 (which are only linked by `IdentU` and `TieGlobal`).

Corrected row text replaces the table summary with the statement below.

> The record holds numbers `D.w u0 j ρ` (positive under `HidaSetting`). For all `u0` and `u`, `Count5` bounds `Real.log (D.T u0 u)` from below by `(∑ j, (1/f) * ∑ ρ, Real.log (D.w u0 j ρ * D.v / π)) + m * D.lg - C.cCount * (D.La + m^2 * D.La / D.k)`, from above by `C.cCount * m * D.L`, and in variation across `u'` by `C.cCount * Real.log D.k`. `D.Main u0` sums over `j` in `Fin m` and `t` in `Top` the term `D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL - (1/f) * ∑ ρ, Real.log (D.w u0 j ρ))`.

### Row 9.1 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean` lines 41-48 and `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean` lines 23-23, 75-77 and `src/Formalism/SizeWindowBrackets/SChain.lean` lines 37-40.

```lean
def CErr (C : Consts) : ℝ := C.eDiv + C.eLoss + 3

def errorBracketSizeWindows (x ε : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))

def BNBounds {W : H → Type} {Top : Type} {m f : ℕ} (Dd : Data H W Top m f) (T2 : Finset H) : Prop :=
  Dd.B0 ≤ (2 * (Fintype.card H : ℝ)) * m * Dd.b * Dd.x ^ Dd.ε ∧
  Dd.Nc ≤ (T2.card : ℝ) * Dd.k * Dd.b * Dd.x ^ Dd.ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * Dd.x ^ (-Dd.ε)))
```

In `errorBracketSizeWindows`, there are no symbols `B` and `N`, because the definition writes `(2 * n) * m * b * x ^ ε` and `nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))` explicitly. In `ch_top`, the exponent constant is `CErr C = C.eDiv + C.eLoss + 3`, `nT` is passed as `TT.card` (tied to `Dd.nT` via `IdentU`), `aE` is passed as `Dd.a` (`aE` is a parameter of `errorBracketSizeWindows` rather than a field name of `Data`), and `ch_top` uses `BNBoundsU` rather than `BNBounds`. Neither `BNBounds` nor `Data` labels `B0` and `Nc` as budgets.

Corrected row text replaces the table summary with the statement below.

> Under `IdentU`, `SizeData₂`, `ErrWindows`, `BNBoundsU`, and `LargeX`, `ch_top` bounds `gapA D N ell TT a w (tr u)` by `Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a`, where `CErr C = C.eDiv + C.eLoss + 3` and `errorBracketSizeWindows` equals `nT * aE * (1 + m^2 / k) + m * (2 * n * m * b * x^ε + nT2 * k * b * x^ε / (n * (n * x^(-ε))))`. `BNBounds` bounds `Dd.B0` and `Dd.Nc` by those two inner summands.

### Row 9.3 (differs)

Lean source checked in `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean` lines 242-327 and `src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` lines 111-124 and `src/Formalism/SizeWindowBrackets/SChain.lean` lines 57-62.

```lean
def SizeWindows (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧ nT2 ≤ n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧
  x * m ≤ k ∧ k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) ∧
  Err ≤ x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))) ∧
  26 ≤ x ^ (3 * ε / 8)

def GrowthSizeBound : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)

def RestSize (ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : Prop :=
  aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧
  k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)
```

First, `proposition_size_bound` takes `SizeWindows` (not `RestSize`) as its premise, and `RestSize` states only `x^(1/2 - ε) ≤ m` without `m ≤ x^(1/2 + ε/2)`, `x * m ≤ k`, `nT2 ≤ n`, `3 ≤ x`, `26 ≤ x^(3ε/8)`, or the `Err` bound. Second, the proof of `proposition_size_bound` does not literally divide `Err` by a multiple of `m`, instead factoring `nT * m * b` out on the upper bound of `Err` via `SZ.T1` through `SZ.T4`, cancelling `nT * m * b` via `le_of_mul_le_mul_left`, multiplying by `2`, and absorbing `nT2 / n` via `1 ≤ x ^ ε * (nT2 / n)`. Third, the row omits both the inequality premise and the conclusion `Gx ≤ x^(1/2 + (C + 3)ε)` of `proposition_size_bound`.

Corrected row text replaces the table summary with the statement below.

> `proposition_size_bound` has type `GrowthSizeBound`, whose premise `SizeWindows` requires `x^(1/2 - ε) ≤ m ≤ x^(1/2 + ε/2)`, `x * m ≤ k`, `nT2 ≤ n`, `3 ≤ x`, `26 ≤ x^(3ε/8)`, bounds on `aE`, `nT`, `nT2`, `k`, and `Err`, and the inequality `nT * m * b * ((nT2 / n) / 2) * (Gx - 4 * x^(1/2 + ε)) ≤ Err + 2 * nT * m * b / x`, concluding `Gx ≤ x^(1/2 + (C + 3)ε)`. Its proof pulls out `nT * m * b` on the upper bound of `Err` via `SZ.T1` through `SZ.T4`, cancels `nT * m * b`, and uses `1 ≤ x^ε * (nT2 / n)`. `RestSize` states only the five lower or upper bounds `aE ≤ 2 * x * b`, `x^(-(ε/8)) * n / 2 ≤ nT`, `x^(-ε) ≤ nT2 / n`, `x^(1/2 - ε) ≤ m`, and `k ≤ n^2 * x^(1/2 - ε)`.

### Row 9.4 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` lines 355-355 and `src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` lines 121-124 and `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean` lines 242-242.

```lean
      GmA D ell Kp c x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) + SigA D ell A0 Kp x

def GrowthSizeBound : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)
```

`ch_core` bounds `GmA D ell Kp c x` by `x ^ (1 / 2 + (C + 3) * ε) + SigA D ell A0 Kp x`, so omitting `+ SigA D ell A0 Kp x` makes the stated bound stronger than what `ch_core` proves. Meanwhile `proposition_size_bound` is a real-variable inequality concluding `Gx ≤ x ^ (1 / 2 + (C + 3) * ε)` and contains no characters in its statement.

Corrected row text replaces the table summary with the statement below.

> The conclusion of `ch_core` is `GmA D ell Kp c x ≤ x^(1/2 + (C + 3)ε) + SigA D ell A0 Kp x` for the weighted kept-character sum `GmA` plus `SigA`, and `proposition_size_bound` concludes `Gx ≤ x^(1/2 + (C + 3)ε)` for a real number `Gx`.

### Row 6.1 (differs)

Lean source checked in `src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean` lines 67-86, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean` lines 19-37, and `src/Formalism/LocalRingCardinality/DataArith.lean` lines 64-105.

```lean
def TieLocal (pt : φ.A → Fm.Ix x) {Top : Type}
    (Dd : Data φ.A (fun u0 => (Fm.D x (pt u0)).what₂.Word) Top m f) : Prop :=
  ∀ u0 : φ.A,
    (∀ u : (Fm.D x (pt u0)).what₂.Word,
      Dd.d u0 u = (((Fm.D x (pt u0)).div.Nu u).rank : ℝ) ∧
      Dd.T u0 u = (((Fm.D x (pt u0)).mem u).A.T : ℝ) ∧
      Dd.muN u0 u = ((Fm.D x (pt u0)).div.Nu u).mu ∧
      Dd.muMaxN u0 u = ((Fm.D x (pt u0)).div.Nu u).muMax ∧
      Dd.h u0 u = (Fm.D x (pt u0)).div.h u ∧
      Dd.muM u0 u = (((Fm.D x (pt u0)).fm u).lat 0).mu ∧
      Dd.muMaxM u0 u = (((Fm.D x (pt u0)).fm u).lat 0).muMax ∧
      ∀ j : Fin m, Dd.EeJ u0 u j =
        ∑ w ∈ (Fm.L x (pt u0)).supp, SizeData₂.sz w ((Fm.L x (pt u0)).E u (j.val + 1) w)) ∧
    Dd.muCC u0 = (Fm.D x (pt u0)).div.RR.muDual ∧
    Dd.muMinCC u0 = (Fm.D x (pt u0)).div.RR.muMinDual ∧
    Dd.Fo u0 = (Fm.L x (pt u0)).Fo ∧ Dd.Ga u0 = (Fm.L x (pt u0)).Ga ∧
    Dd.Ta u0 = ∑ w ∈ (Fm.L x (pt u0)).supp, SizeData₂.sz w ((Fm.L x (pt u0)).tau w) ∧
    Dd.IO u0 = ∑ w ∈ (Fm.L x (pt u0)).supp,
      SizeData₂.lwP w * ((Fm.D x (pt u0)).what₂.places.ramIdx w : ℝ) * (Fm.L x (pt u0)).io w ∧
    Dd.del u0 = (Fm.D x (pt u0)).what₂.delp
```

The predicate `TieLocal` takes a function `pt` from the finite additive commutative group `φ.A` to `Fm.Ix x` and a `Data` record `Dd` whose second index at `u0` runs over `(Fm.D x (pt u0)).what₂.Word`, rather than asserting that each group element has its own distinct datum. Beyond equating `Dd.muCC u0` with `div.RR.muDual` and `Dd.muN u0 u` with `(div.Nu u).mu`, `TieLocal` also binds thirteen further fields of `Dd`, namely `d`, `T`, `muMaxN`, `h`, `muM`, `muMaxM`, `EeJ`, `muMinCC`, `Fo`, `Ga`, `Ta`, `IO`, and `del`. Both `div.RR` and `div.Nu u` have type `HLat`, which bundles a basis `b`, infinite-place matrices `X`, and an integer-ring submodule `L`, and calling an `HLat` a Hermitian lattice is an interpretation.

Corrected row text replaces the table summary with the statement below.

> Given a map `pt` sending each element `u0` of the finite additive commutative group `φ.A` to a datum index `pt u0` of a family `Fm` and a record `Dd` whose index `u` at `u0` runs over `(Fm.D x (pt u0)).what₂.Word`, the condition `TieLocal` equates `muCC u0` with `div.RR.muDual` and `muN u0 u` with `(div.Nu u).mu` for the `HLat` records `div.RR` and `div.Nu u`, and also ties thirteen further fields of `Dd`, namely `d`, `T`, `muMaxN`, `h`, `muM`, `muMaxM`, `EeJ`, `muMinCC`, `Fo`, `Ga`, `Ta`, `IO`, and `del`.

### Row 6.2 (differs)

Lean source checked in `src/Formalism/LatticeSlopes/Statement.lean` lines 19-30, `src/Formalism/HarderNarasimhan/Statement.lean` lines 19-28, and `src/Formalism/HarderNarasimhan/StatementPl.lean` lines 29 and 68-69.

```lean
def covol (L : Submodule ℤ E) : ℝ := by
  classical
  exact if h : DiscreteTopology L then
    haveI := h
    Real.sqrt (Matrix.gram ℝ (fun i => ((Module.finBasis ℤ L i : L) : E))).det
  else 0

def rk (L : Submodule ℤ E) : ℕ := Module.finrank ℤ L

def deg (L : Submodule ℤ E) : ℝ := -Real.log (covol L)

def slope (L : Submodule ℤ E) : ℝ := deg L / (rk L : ℝ)

def logDisc : ℝ := Real.log |(NumberField.discr K : ℝ)|

def muDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  2 * slope (Formalism.HermitianLatticesTheory.realize b X) L - Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)
```

First, the declaration `covol` defines only the square root of the Gram determinant of a `ℤ`-basis of `L` when `DiscreteTopology L` holds and returns `0` otherwise, whereas the quotient `-Real.log (covol L) / (rk L)` is defined in `Formalism.F.slope` using `Formalism.F.deg` and `Formalism.F.rk`, which are omitted from the declarations list. Second, `muDef` does not take a Hermitian lattice structure as an argument, and instead takes a `K`-basis `b`, infinite-place matrices `X`, and an `(𝓞 K)`-submodule `L`, maps `L` into real inner product space via `Formalism.HermitianLatticesTheory.realize b X`, and computes `2 * Formalism.HN.slope (realize b X) L - Real.log 2 + logDisc K / Module.finrank ℚ K`, where `logDisc K` is `Real.log |(NumberField.discr K)|` and `Module.finrank ℚ K` is the degree of `K` over `ℚ`. Treating `(b, X, L)` as a Hermitian lattice is an interpretation.

Corrected row text replaces the table summary with the statement below.

> For a `ℤ`-submodule `L` of a finite-dimensional real inner product space, `covol L` is the square root of the Gram determinant when `DiscreteTopology L` holds and `0` otherwise, and `Formalism.F.slope L` is `-Real.log (covol L)` divided by `Formalism.F.rk L`. For a `K`-basis `b`, infinite-place matrices `X`, and an `(𝓞 K)`-submodule `L`, `muDef b X L` realizes `L` into real inner product space via `realize b X` and computes twice `Formalism.HN.slope (realize b X) L`, minus `Real.log 2`, plus `Real.log |(NumberField.discr K)|` divided by `Module.finrank ℚ K`.

### Row 6.3 (says less)

Lean source checked in `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean` lines 132-137, `src/Formalism/LocalRingCardinality/DataArith.lean` lines 149 and 171, and `src/Formalism/HarderNarasimhan/StatementPl.lean` lines 25 and 59-66.

```lean
def WordFacts {D : D7} (L : SizeData₂ D) (C Cabs : ℝ) (u : D.what₂.Word) : Prop :=
  (D.div.Nu u).L.map ((D.div.Bk u).restrictScalars (𝓞 D.what₂.LL)) ≤ D.div.cc ∧
  (D.div.Bk u ≠ 0 → Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤
    D.div.h u) ∧
  D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u +
    C * (D.host.TT.card : ℝ) * L.sc.a * L.La + C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)

def htMap (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) : ℝ :=
  (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)
```

For a fixed word `u`, `WordFacts L C Cabs u` states three conjuncts, and the row omits the third conjunct completely, which is the inequality `D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u + C * D.host.TT.card * L.sc.a * L.La + C * D.R.m * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)`. In addition, `D.div.Bk u` is a field of `DivData` defined as a `K`-linear map between the ambient vector spaces `(D.div.Nu u).V` and `Module.Dual K D.div.RR.V` whose restriction maps `(D.div.Nu u).L` into `D.div.cc` (defined as `D.div.RR.dualL`), rather than a map with domain the lattice itself, and `htMap` uses `opNormAt` with the bases and frames of `D.div.Nu u` and `D.div.RR.dualB`, `D.div.RR.dualX`.

Corrected row text replaces the table summary with the statement below.

> In `DivData`, each word `u` has a linear map `Bk u` between the ambient vector spaces of `Nu u` and the dual of `RR`. For a word `u`, `WordFacts` states three conditions, namely that `Bk u` maps `(Nu u).L` into `cc` (`RR.dualL`), that when `Bk u` is nonzero `htMap` (the mean over infinite places of `Real.log (opNormAt ... ^ 2)`) is at most `div.h u`, and that `RR.muDual + div.h u - L.Fo` stays below `L.MAIN u` plus the two error terms of `WordFacts`.

### Row 6.4 (differs)

Lean source checked in `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean` lines 192-277, `src/Formalism/LocalToGlobal/Columns/FiniteSumNonzeroLargeDepth.lean` lines 226-248, 419, 613-637, 1088-1097, and 1242-1245, `src/Formalism/LocalToGlobal/Columns/ColForms.lean` line 49, `src/Formalism/LocalToGlobal/Columns/RowForms.lean` line 258, `src/Formalism/LocalRingCardinality/Params.lean` line 40, and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RowsUOfColPins.lean` lines 30-99.

```lean
def evRho (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) :
    FormG (rowTy Ch sel mu P).inv →* Module.End X.K (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V where
  toFun a := ((((rowTy Ch sel mu P).inv.chr a.2)⁻¹ : X.Kˣ) : X.K) •
    (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) a.1)

@[reducible] def evGSD (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) : GSD X.K where
  G := FormG (rowTy Ch sel mu P).inv
  D := RowPt Pr R sel mu
  actD := formAct (rowTy Ch sel mu P).inv

abbrev FrmG (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : Type := UF X.E n × ↥Λ.grp × ↥Θ.grp

abbrev FormG (Λ : LevFam X.E X.K n SG) : Type := UF X.E n × ↥Λ.grp

def rowTy (P : LevFam X.E X.K R.r Pr.vGs) : LevFam X.E X.K (R.N R.m - 1) (rowSG Pr sel mu) :=
```

Two parts differ from the Lean text. First, on the spaces of `KerChain.ofCol`, only the `GFam` spaces `chF` for indices `0` through `m - 1` (`m2 + 1` under `R.m = m2 + 2`) carry groups `FrmG` of the form `UF X.E (R.N j)` times two subgroups `(L.levG j b).grp` and `(L.levQ j b).grp`, whereas the final space `Q.S₁` (`evGSD`) carries `FormG (rowTy Ch sel mu P).inv`, which is `UF X.E (R.N R.m - 1)` times a single subgroup `(rowTy Ch sel mu P).inv.grp`, acting on `evGSD.V` via the embedding `extUH` into `UF X.E (R.N R.m)`. Second, `rowsU_of_colPins_alt` is proved per word `u` under explicit hypotheses such as `KerTies`, `KerSizes`, `NprimeDef`, `NuFull`, `0 < rank`, and `C0 ≤ Ch`, factoring the pairing `Dc.Pt` through `ColChain`, and also produces `FirstCols`, `X0`, `HtNums`, norm bounds on `PtL` and `cb.sq`, determinant unit conditions, and `IsLattice`, while `ChainTie` adds metric equalities `metF` and `metL` and operator equalities `kerF` and `kerC`. Calling `UF` a unitary group and `ThDist` a theta kernel are interpretations.

Corrected row text replaces the table summary with the statement below.

> Under its hypotheses for a word `u`, `rowsU_of_colPins_alt` builds a `ColChain` factoring `Dc.Pt w Bs.μ0` together with a `ChainTie` linking it via metric and operator equalities (`metF`, `metL`, `kerF`, `kerC`) to a `KerChain`, plus `FirstCols`, `HtNums`, and norm bounds. In `KerChain.ofCol`, `chF` uses `FrmG` (`UF X.E (R.N j)` with `R.N j = R.k + j * (R.t + 1)` and two subgroups) up to `m - 1`, while the end space `evGSD` uses `FormG` with `UF X.E (R.N R.m - 1)` embedded into `UF X.E (R.N R.m)` and one glued subgroup, and `ChTh` holds `m` distributions `ThDist` (`th i` for `i` from `0` to `m2` and `top` from `N (m2 + 1)` to `N R.m`).

### Row 6.5 (differs)

Lean source checked in `src/Formalism/LocalToGlobal/Columns/FiniteSumNonzeroLargeDepth.lean` lines 300-304 and 993-1079, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean` lines 220-250, and `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerChainMatricesWithNormBounds.lean` lines 63-69, 102-104, and 177-196.

```lean
def CplKer.comp {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (h : S.Ok) (s : S.Sec) : ClsKer S₀ S₁ where
  k d₀ d₁ :=
    letI := h.fintypeCl
    ∑ c : S.Cl, (((S.toCSDOf h s).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (s.rep c)).toFinset, (A.k2 (s.rep c) y d₁) ∘ₗ (A.k1 d₀ (s.rep c) y)

structure ChIdx.Ok (G : ChGlob X R.m) (m2 : ℕ) : Prop where
  hm : R.m = m2 + 2

def KjN : ∀ j : Fin (Q.n + 1), Matrix (Fin (bund Dc u Q nF XF nS XS (j.val + 1)).1) (Fin (bund Dc u Q nF XF nS XS j.val).1) K :=
  Fin.lastCases (motive := fun j : Fin (Q.n + 1) =>
      Matrix (Fin (bund Dc u Q nF XF nS XS (j.val + 1)).1) (Fin (bund Dc u Q nF XF nS XS j.val).1) K)
    (LinearMap.toMatrix' ((eL Dc u Q nF XF nS eS XS Q.n (by omega)).symm.toLinearMap ∘ₗ Q.cpl ∘ₗ
      coFN Dc u Q f0 nF eF XF nS XS Q.n le_rfl))
    (fun i => LinearMap.toMatrix' ((eN Dc u Q nF eF XF nS XS i.val i.isLt).symm.toLinearMap ∘ₗ Q.step i.val ∘ₗ
      coFN Dc u Q f0 nF eF XF nS XS i.val i.isLt.le))
```

`chainOf` constructs `Q.n + 1` matrices `KjN` for an arbitrary `KerChain` `Q`, where the first `Q.n` matrices represent single step operators `Q.step i` (multiplied sequentially by `chainMat` in `fact`) and the last represents `Q.cpl`, followed by `PtL` built from `g`. The count `Q.n + 1 = m - 1` (and tying `Q.step` and `Q.cpl` to `matK`, `cp1K`, and `cp2K`) holds when `Q` is `KerChain.ofCol` built from `chKer` and `ChIdx.Ok.hm` gives `R.m = m2 + 2`, while `ChIdx.Ok` also imposes over thirty further compatibility, nonvanishing, stabilizer, depth, and character conditions omitted from the row. Moreover, `CplKer.comp` builds a `ClsKer` for any `CplKer` by summing over orbits `c` in `S.Cl` with outer weight `(wt c)⁻¹` applied to an unweighted finite sum over `y` of `A.k2 ∘ₗ A.k1`, and `KerChain.cpl` then sums `opOf` over `(Q.F Q.n).β` before `chainOf` turns `Q.cpl` into the last matrix.

Corrected row text replaces the table summary with the statement below.

> `chainOf` turns any `KerChain` `Q` into `Q.n + 1` matrices `KjN` (representing `Q.step i` for `i < Q.n` and `Q.cpl` at `Q.n`) followed by `PtL` formed from `g`. Under `ChIdx.Ok` (which states `R.m = m2 + 2` alongside thirty-one compatibility, nonvanishing, stabilizer, depth, and character conditions), `KerChain.ofCol` gives `Q.n = m2 = R.m - 2` steps and `m - 1` matrices, and `CplKer.comp` forms the coupled `ClsKer` by weighting each orbit `c` by `(wt c)⁻¹` times a finite sum over `y` of `k2 ∘ₗ k1`, which `KerChain.cpl` sums over `(Q.F Q.n).β` into the last matrix.

### Row 7.1 (differs)

Lean source checked in `src/Formalism/LocalToGlobal/Divisibility/NumbersLink.lean` lines 34-43 and 392-398, and `src/Formalism/LocalToGlobal/Divisibility/Numbers.lean` lines 159-173 and 195-196.

```lean
def aTPl (ρ : RPl N.R) : ℝ := ((N.aT ρ.2 : ℚ) : ℝ)
def eEN (δ : Code N) (j : ℕ) (ρ : RPl N.R) : ℝ :=
  (∑ i, ph (N.nuPad δ j ρ i)) - N.logHook j ρ - (if ρ ∈ N.topsPl then ph (N.aTPl ρ) else 0)
def dN (δ : Code N) (j : ℕ) (ρ : RPl N.R) : ℝ :=
  (∑ i, N.nuPad δ j ρ i) - (if ρ ∈ N.topsPl then N.aTPl ρ else 0) - (N.R.k : ℝ) * N.w j ρ
theorem stepE_num (δ : Code N) {Nc lam0 C0 ce Ch Sw C1 : ℝ} (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1)
    (j : Fin N.R.m) (ρ : RPl N.R) :
    N.eEN δ (j.1 + 1) ρ ≤
        C0 * (N.w (j.1 + 1) ρ + N.Sc + (N.Nm : ℝ) ^ 2 + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) * N.eta) * N.La ∧
      |N.dN δ (j.1 + 1) ρ| ≤
        C0 * (N.w (j.1 + 1) ρ + (N.R.k : ℝ) * ((N.Nm : ℝ) + N.Sc) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) * N.eta +
          (if ρ ∈ N.topsPl then (N.R.k : ℝ) * N.sc.b' else 0)) := by
def aT (t : N.R.A) : ℚ :=
  (N.hc (false, t)).u ⟨0, by have := N.R.m_add_three_le_k; omega⟩ - ((N.R.k : ℚ) - 1) / 2
```

Row 7.1 differs from stepE_num in three respects. First, stepE_num requires a word code delta of type Code N and an explicit record of hypotheses H of type N.NumFacts, rather than holding unconditionally for every lift and place. Second, stepE_num proves a conjunction that both gives an explicit upper bound on N.eEN and bounds |N.dN|, whereas Row 7.1 omits |N.dN| and replaces the explicit N.eEN bound with an unspecified error term. Third, Row 7.1 calls a the top weight of the place, whereas N.aTPl rho equals ((N.aT rho.2 as rational) as real) with N.aT t equal to (N.hc (false, t)).u 0 minus (k minus 1) divided by 2, while the lift weight N.nu delta j (false, t) 0 is N.aT t plus N.w j (false, t) minus (k plus (2 times j minus 1) times (t plus 1)) divided by 2.

Corrected row text replaces the table summary with the statement below.

> Given a word code delta and hypotheses NumFacts on a datum N, stepE_num proves for every lift j and every place rho that eEN (the sum of y times log y minus y over the padded weights nuPad, minus logHook j rho, and minus y times log y minus y at aTPl rho when rho lies in topsPl) is at most C0 times (w plus Sc plus Nm squared plus m times (t plus 1) times eta) times La, and that the absolute value of dN (the sum of nuPad minus aTPl rho when rho lies in topsPl minus k times w) is at most C0 times (w plus k times (Nm plus Sc) plus m times (t plus 1) times eta plus k times b' when rho lies in topsPl). Here aTPl rho comes from u 0 minus (k minus 1) divided by 2 at (false, rho.2), and logHook is the logarithm of the hook product of apDiag.

### Row 7.3 (says less)

Lean source checked in `src/Formalism/LocalToGlobal/Divisibility/NumbersLink.lean` lines 79-80 and 428-478, `src/Formalism/LocalToGlobal/Divisibility/Numbers.lean` lines 159-162, and `src/Formalism/QuotientMetricDivisors/TheoremDivIneqRowsShift.lean` line 98.

```lean
  inter : ∀ z (i : ℕ) (h : i + 1 < N.R.k),
    N.sigPar z i < N.uW δ z ⟨i, by omega⟩ ∧ N.uW δ z ⟨i + 1, h⟩ < N.sigPar z i
def uW (δ : Code N) (z : RPl N.R) (i : Fin N.R.k) : ℚ :=
  if h : 1 ≤ i.1 ∧ i.1 + 1 < N.R.k then
    (N.hc z).v ⟨i.1 - 1, by omega⟩ - 1 / 2 - (if δ ⟨i.1 - 1, by omega⟩ then (N.Del : ℚ) else 0)
  else (N.hc z).u i
    (∀ ρ, ∀ i : Fin (n + 1), v ρ i < u ρ i.castSucc ∧ u ρ i.succ < v ρ i) →
```

Row 7.3 under-specifies the interlacing premise and the surrounding hypotheses. In Lean, N.uW delta z depends on both the word code delta and the place z rather than on the place alone. Furthermore, inter and RowsStepEOrigin require indexed strict inequalities sigPar z i less than uW delta z i and uW delta z (i plus 1) less than sigPar z i between two tuples of lengths k and k minus 1 rather than unordered sets, and interlacing is one among several premises in NumFacts and RowsStepEOrigin.

Corrected row text replaces the table summary with the statement below.

> The bound of 7.1 takes as premises NumFacts (and through young_diagram_step_origin the remaining hypotheses of RowsStepEOrigin), which include the indexed strict interlacing inter between the k numbers uW delta z (depending on both the word code delta and the place z) and the first k minus 1 numbers sigPar z of the place.

### Row 8.1 (says less)

Lean source checked in `src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean` lines 192-197, `src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean` lines 502-505 and 560-564, `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 182-206, and `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean` lines 262-266.

```lean
def Frame_at (D : D7) (etaB eB : ℝ) : Prop :=
  ∃ η e : ℝ, 0 ≤ η ∧ η ≤ etaB ∧ 0 ≤ e ∧ e ≤ eB ∧
    ∀ HH : ℝ, sFrame D.div.Nu D.div.h - D.div.RR.muMinDual ≤ HH → 0 < HH →
      sFrame D.div.Nu D.div.h - Real.log (Fintype.card D.what₂.Word : ℝ) -
        (1 - D.what₂.delp)⁻¹ * (4 * uFrame D.div.Nu D.div.h * Real.log (1 + HH / uFrame D.div.Nu D.div.h) +
          (η + 4 * Real.sqrt e) * HH) ≤ D.div.RR.muDual

theorem frame_at_of {D : D7} (L : SizeData₂ D) (C0 CH sg de eB : ℝ) (hsgx : sg = L.sc.x ^ (-CH)) (hsg20 : sg ≤ 1 / 20)
    (hde0 : 0 ≤ de) (hde4 : de ≤ 1 / 4) (hC0 : 1 ≤ C0)
    (hR : FrameReal_at D sg de eB) (hP : ChProviso_at L C0) (hCo : ChCode_at L C0 CH) (hFull : D.NuFull)
    (hLat : Lat_at D) : Frame_at D (5 * sg + 3 * Real.sqrt de) eB := by
...
  exact joint_a_ramified_holds D.what₂.LL (Module.Dual D.what₂.LL D.div.RR.V) D.div.RR.ι κ₁ D.what₂.Word
    (fun u => (D.div.Nu u).V) (fun u => (D.div.Nu u).ι) D.div.RR.dualB D.div.RR.dualX D.div.RR.dualL
    (fun u => (D.div.Nu u).b) (fun u => (D.div.Nu u).X) (fun u => (D.div.Nu u).L) D.div.Bk D.div.h v Y Y' Ball γ ιf Bf Vr
    _ _ HH D.what₂.delp D.what₂.Dstar sg η0 η1 e0 de hG hNum hγ hBV hV hD0 hsg0 hsg20 hRs h0 h0' h1 he0 hse hde0 hde4
    hcor hS
```

The Lean theorem `frame_at_of` does not derive `Frame_at` unconditionally from `JointARam`. It requires `FrameReal_at D sg de eB`, `ChProviso_at L C0`, `ChCode_at L C0 CH`, `D.NuFull`, `Lat_at D`, and parameter hypotheses (`sg = L.sc.x ^ (-CH)`, `sg ≤ 1 / 20`, `0 ≤ de ≤ 1 / 4`, `1 ≤ C0`), and concludes `Frame_at D (5 * sg + 3 * Real.sqrt de) eB`. In addition, `JointARam` applies to Hermitian lattices over a totally complex number field, and `frame_at_of` passes `D.div.RR.dualL` as the target lattice and `fun u => (D.div.Nu u).L` as the family lattices.

Corrected row text replaces the table summary with the statement below.

> The slope inequality `Frame_at` for the dual lattice of `RR` and the word lattices `Nu u` over the totally complex number field `LL` follows from `JointARam` when `FrameReal_at`, `ChProviso_at`, `ChCode_at`, `NuFull`, `Lat_at`, and parameter bounds on `sg`, `de`, and `C0` hold, yielding `Frame_at` with parameter `5 * sg + 3 * √de`. The proof applies `joint_a_ramified_holds` with the words of the datum as the family, the dual lattice of `RR` as the target, and the maps of 6.3 as the maps.

### Row 8.2 (differs)

Lean source checked in `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 34-39, 63-94, and 182-206.

```lean
def InputSG {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (Dstar η0 η1 e0 : ℝ) : Prop :=
  (∀ i j, i ≠ j → hsSq (KpG B ga i j)
      ≤ (1 + η0) * (Fintype.card (ι i) : ℝ) * (Fintype.card (ι j) : ℝ) / Dstar) ∧
  (∀ i, hsSq (KdG B ga i - 1) ≤ e0 * (Fintype.card (ι i) : ℝ)) ∧
  (Fintype.card α : ℝ) ≤ (1 + η1) * Dstar

def LatGeom {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (δ : ℝ) : Prop :=
  (∀ w, IsUnit (X' w).det) ∧ (∀ i w, IsUnit (X i w).det) ∧ (∀ i, IsUnit (Y i).det) ∧
  IsUnit Y'.det ∧
  cc.FG ∧ Submodule.span K (cc : Set W) = ⊤ ∧
  (∀ i, (N i).FG) ∧ (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) ∧
  0 < ∑ i, Fintype.card (ι i) ∧ (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) ∧
  (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) ∧
  0 ≤ δ ∧ δ < 1 ∧ (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) ∧
  (∀ i (k : κ) (j : ι i),
    Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)

def LatNum {K W κ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (h : I → ℝ) (s u HH : ℝ) : Prop :=
  s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
    ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) ∧
  0 ≤ u ∧ (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) ∧
  s - muMinDef b' X' cc ≤ HH ∧ 0 ≤ HH

    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
```

Row 8.2 differs from the Lean text because `InputSG` in `JointARam` is not applied to the matrices of the maps at one infinite place. Instead, `LatGeom` introduces matrices `Ball i` that match the matrices of `B i` at place `v` only on the target rows `Sum.inl k` (while allowing extra rows `κ₁` bounded via `δ`), and `JointARam` factors `Ball i = Bf i * Vr i` with `(Vr i)ᴴ * Vr i = 1` and applies `InputSG` to the first factors `Bf i`, whose column indices `ιf i` may exceed `ι i` with total surplus at most `de * RsG ιf`. In addition, row 8.2 names `LatNum` without stating any of its slope-mean, excess `u`, or `HH` conditions, omits the invertibility, finite-generation, full-rank, positive column sum, and `δ`/`κ₁` conditions of `LatGeom`, and states the `JointARam` bounds `η0, η1, √e0 ≤ sg / 2` and `sg ≤ 1 / 20` as if they belonged to the named definitions while omitting `-1 ≤ η0`, `0 ≤ e0`, `0 < Dstar`, `0 < sg`, and `0 ≤ de ≤ 1 / 4`.

Corrected row text replaces the table summary with the statement below.

> Under `LatGeom`, each map sends its finitely generated full-rank lattice into the finitely generated full-rank target lattice with height at most h when nonzero, and each map has at one infinite place a matrix `Ball` that agrees on the target rows with the map's matrix in invertible frames and has at most δ times all rows as extra rows, with 0 ≤ δ < 1. Under `LatNum`, s is at most the column-weighted mean of `mu` minus h, `muMax` minus h is at most s plus u for u ≥ 0, and HH ≥ 0 is at least s minus the smallest slope of the target. Each `Ball` factors as a first factor `Bf` times an isometry `Vr`, where the excess of `Bf` columns over `Ball` columns sums to at most `de` times all `Bf` columns with 0 ≤ `de` ≤ 1/4. `InputSG` gives three bounds on `Bf` with weights γ > 0 and `Dstar` > 0, namely off-diagonal `hsSq (KpG Bf γ i j) ≤ (1 + η0)·|ιf i|·|ιf j|/`Dstar`, diagonal `hsSq (KdG Bf γ i - 1) ≤ e0·|ιf i|`, and row count at most (1 + η1)·`Dstar`, where `JointARam` takes −1 ≤ η0, 0 ≤ e0, and η0, η1, √e0 ≤ σ/2 for 0 < σ ≤ 1/20.

### Row 8.3 (says less)

Lean source checked in `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 50-61 and 153-164, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean` lines 172-200 and 223-266, `src/Formalism/HarderNarasimhan/StatementFrameF.lean` lines 30-66, and `src/Formalism/HarderNarasimhan/ShiftInvariance.lean` line 63.

```lean
def FrameDeviationLinear {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (e : ℝ) : Prop :=
  (∑ i, hs2 (frK (ga i) (Matrix.toEuclideanLin (B i)) - LinearMap.id)) ≤
    e * ∑ i, (Fintype.card (ι i) : ℝ)

def FrameTraceRatioLinear {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (η : ℝ) : Prop :=
  (LinearMap.trace ℂ (EuclideanSpace ℂ α)
      (frQ ga (fun i => Matrix.toEuclideanLin (B i)) ∘ₗ
       frQ ga (fun i => Matrix.toEuclideanLin (B i)))).re ≤
    (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ α)
      (frQ ga (fun i => Matrix.toEuclideanLin (B i)))).re ^ 2 / (Fintype.card α : ℝ)

def RamLin : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ιf ι : I → Type) [∀ i, Fintype (ιf i)]
    [∀ i, DecidableEq (ιf i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (Bf : ∀ i, Matrix α (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ) (ga : I → ℝ)
    (Dstar sg η0 η1 e0 de : ℝ),
    (∀ i, (Vr i)ᴴ * Vr i = 1) → (∀ i, 0 ≤ ga i) → 0 < Dstar → 0 < sg → sg ≤ 1 / 20 →
    Dstar / sg ≤ RsG ιf → -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf ga Dstar η0 η1 e0 →
    FrameTraceRatioLinear (fun i => Bf i * Vr i) ga (5 * sg + 3 * Real.sqrt de) ∧
    FrameDeviationLinear (fun i => Bf i * Vr i) ga (2 * e0) ∧ 2 * e0 ≤ 1 / 4 ∧ 0 < ∑ i, Fintype.card (ι i)

theorem theoremF : TheoremF := frame_theorem_log_ideal
```

Row 8.3 states less than `ramification_linear_case_holds` (`RamLin`) and `theoremF` (`TheoremF`). First, `RamLin` does not use only the three bounds of `InputSG`, and it uses the isometries `Vr`, the column-sum bound `Dstar / sg ≤ RsG ιf`, the column-surplus bound with `de ≤ 1 / 4`, and the parameter inequalities to shift from `Bf` to `Bf * Vr` with new parameters `5 * sg + 3 * Real.sqrt de` and `2 * e0`, and also proves `2 * e0 ≤ 1 / 4` and `0 < ∑ i, Fintype.card (ι i)`. Second, the row omits the actual inequality forms of `FrameTraceRatioLinear` and `FrameDeviationLinear`. Third, `theoremF` requires all of `LatGeom` (including `Ball`, `δ`, `κ₁`, invertibility, and full rank), all of `LatNum`, positive weights, `0 ≤ e ≤ 1 / 4`, and `0 ≤ η`, rather than only the lattice-map-height subset mentioned in 8.2.

Corrected row text replaces the table summary with the statement below.

> The proof of the general statement has two parts. Using `InputSG` on the first factors together with the isometries `Vr`, the column-sum bound, the column-surplus bound with `de`, and the parameter inequalities, `ramification_linear_case_holds` proves two family conditions for the compressed matrices `Bf i * Vr i` with parameters `5 * sg + 3 * √de` and `2 * e0`, namely that the real part of the trace of `Q²` is at most `(1 + η)` times `(Re tr Q)² / n` and the sum of squared Hilbert-Schmidt distances of the weighted Gram matrices from the identity is at most `e` times the sum of column counts, together with `2 * e0 ≤ 1 / 4` and positive total column count. The second part, `theoremF`, derives the slope inequality from those two conditions together with positive weights, `0 ≤ e ≤ 1 / 4`, `0 ≤ η`, and all premises of `LatGeom` and `LatNum`.

### Row 8.4 (says less)

Lean source checked in `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 208-211, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean` lines 287-300, `src/Formalism/SharpRestriction/GlobalSchurBounds/Chosen.lean` lines 18, 57-61, and 83-88, `src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean` lines 144-147, and `src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean` lines 513-526.

```lean
def WordsR : Prop :=
  ∀ (I : Type) [Fintype I] (ιf : I → Type) [∀ i, Fintype (ιf i)] (Dstar sg C0 Gam : ℝ),
    0 < Dstar → 0 < sg → 0 < C0 → 0 < Gam → C0 * Gam ^ 2 / sg ≤ (Fintype.card I : ℝ) →
    (∀ i, Dstar * (Gam ^ 2)⁻¹ / C0 ≤ (Fintype.card (ιf i) : ℝ)) → Dstar / sg ≤ RsG ιf

def GamL : ℝ := Real.exp (L.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L)

def ChProviso_at (C0 : ℝ) : Prop :=
  ∀ u, C0⁻¹ ≤ (D.duS u : ℝ) * GamL L ^ 2 / D.what₂.Dstar ∧ (D.duS u : ℝ) * GamL L ^ 2 / D.what₂.Dstar ≤ C0

def ChCode_at (C0 CH : ℝ) : Prop :=
  C0 * GamL L ^ 2 * L.sc.x ^ CH ≤ (Fintype.card D.what₂.Word : ℝ)

def DesignExists (𝒞 : FamClass) (C0 : ℝ) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → ∀ K : TransportedAlt, ∃ (Fm : FamP eps) (CH : ℝ),
    𝒞 Fm ∧ 0 ≤ CH ∧ Fm.Large K CH ∧ ChosenE Fm C0 CH ∧ TuSize Fm ∧
      DGamSize Fm
```

Row 8.4 omits several parts of the named declarations. First, `RsG ιf` in `word_count_bound_holds` and `D.duS u` in `ChProviso_at` count the columns of the first factors `Bf u` (`Fintype.card (ιf u) = D.duS u`), not the lattice-map columns `(D.div.Nu u).ι`. Second, `ChProviso_at`, `ChCode_at`, and `GamL` take `L` of type `SizeData₂ D` (using `L.CGam` and `L.sc.L`, though `gamL_eq` equates `GamL L` to `(D.mem u).A.GamP`), and `word_count_bound_holds` uses `0 < Dstar`, `0 < sg`, `0 < C0`, `0 < Gam`, `sg = L.sc.x ^ (-CH)` (in `frame_at_of`), and only the lower inequality of `ChProviso_at`. Third, `DesignExists` is a parameterized predicate (used as a premise in `topDesWin`) that asserts much more than the existence of families with `ChProviso_at` and `ChCode_at`, including `ε0`, `K`, `𝒞 Fm`, `0 ≤ CH`, `Fm.Large K CH`, all seven parts of `Chosen` eventually in `x`, `TuSize`, and `DGamSize`.

Corrected row text replaces the table summary with the statement below.

> The general statement also needs the column counts of the first factors to sum to at least `Dstar`/σ. Under 0 < `Dstar`, 0 < σ, 0 < C0, 0 < Γ, and σ = x^(−CH), `word_count_bound_holds` derives this from the lower bound of `ChProviso_at` (which places `duS u`·Γ²/`Dstar` between 1/C0 and C0 for a `SizeData₂` record L with Γ = `GamL L`) and from `ChCode_at` (which states that the words number at least C0·Γ²·x^CH). For a family class 𝒞 and constant C0, `DesignExists` (a premise of `topDesWin`) states that there exists ε0 > 0 such that for every 0 < ε ≤ ε0 and `TransportedAlt` bound K there exist a family in 𝒞 and CH ≥ 0 satisfying `Fm.Large K CH`, `ChosenE Fm C0 CH` (which gives `ChProviso_at` and `ChCode_at` eventually in x alongside five further conditions), `TuSize`, and `DGamSize`.

### Row 8.5 (differs)

Lean source checked in `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean` lines 134-148, `src/Formalism/LocalRingCardinality/DataParamsS.lean` line 12, `src/Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean` lines 330-336, 489, and 499, and `src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean` lines 771-783, 818-820, 1051-1071, 1251-1283, and 1316-1359.

```lean
def hsDiagFull (D : D7) (u : D.what₂.Word) : ℝ :=
  S.hsNormSq (S.KD D u u - ContinuousLinearMap.id ℂ (D.s.Cu u))

def LinkS_at {D : D7} (L : SizeData₂ D) (C0 Gam eta0 eta1 e0 : ℝ) : Prop :=
  (∀ u, C0⁻¹ ≤ (D.duS u : ℝ) * Gam ^ 2 / D.what₂.Dstar ∧ (D.duS u : ℝ) * Gam ^ 2 / D.what₂.Dstar ≤ C0) →
  (∀ u u', u ≠ u' → L.hsSq u u' ≤ (1 + eta0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) ∧
  (∀ u, hsDiagFull D u ≤ e0 * (D.duS u : ℝ)) ∧ (D.what₂.Dall : ℝ) ≤ (1 + eta1) * D.what₂.Dstar

def LinkS {eps : ℝ} (Fm : FamP eps) (C0 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ eta0 eta1 e0 : ℝ, 0 ≤ e0 ∧
    eta0 ≤ Real.exp (-(x ^ (eps / 8))) ∧ eta1 ≤ Real.exp (-(x ^ (eps / 8))) ∧
    Real.sqrt e0 ≤ Real.exp (-(x ^ (eps / 8))) ∧
    LinkS_at (Fm.L x i) C0 (GamOf (Fm.L x i)) eta0 eta1 e0

def MatK_at (D : D7) (η0 e0 : ℝ) : Prop :=
  ∃ (v : InfinitePlace D.what₂.LL)
    (Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ) (Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ)
    (Ball : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) (D.div.Nu u).ι ℂ) (γ : D.what₂.Word → ℝ)
    (Bf : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) (Fin (D.duS u)) ℂ)
    (Vr : ∀ u, Matrix (Fin (D.duS u)) (D.div.Nu u).ι ℂ),
    (∀ u, IsUnit (Y u).det) ∧ IsUnit Y'.det ∧
    (∀ u (k : D.div.RR.ι) (j : (D.div.Nu u).ι), Ball u (Sum.inl k) j =
      (Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map v.embedding * Y u) k j) ∧
    (∀ u, 0 < γ u) ∧ (∀ u, Ball u = Bf u * Vr u) ∧ (∀ u, (Vr u)ᴴ * Vr u = 1) ∧
    (∀ u u', u ≠ u' → Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq (KpG Bf γ u u') ≤
      (1 + η0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) ∧
    (∀ u, Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq (KdG Bf γ u - 1) ≤ e0 * (D.duS u : ℝ))

def BlockReal_at (D : D7) : Prop :=
  ∃ (ε : ℂ →+* ℂ) (_ : IsIdOrConj ε) (f : OrthonormalBasis (RowIx D) ℂ D.s.HH) (v : InfinitePlace D.what₂.LL)
    (Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ) (Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ)
    (Vr : ∀ u, Matrix (Fin (D.duS u)) (D.div.Nu u).ι ℂ),
    (∀ u, IsUnit (Y u).det) ∧ IsUnit Y'.det ∧ (∀ u, (Vr u)ᴴ * Vr u = 1) ∧
    ∀ u (k : D.div.RR.ι) (j : (D.div.Nu u).ι), ((PMat D f u).map ε * Vr u) (Sum.inl k) j =
      (Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map v.embedding * Y u) k j

theorem matK_at_of {D : D7} (L : SizeData₂ D) (η0 e0 : ℝ) (hB : BlockReal_at D) (hc : UnfoldingConstantsPos D)
    (h1 : ∀ u u', u ≠ u' → L.hsSq u u' ≤ (1 + η0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar)
    (h2 : ∀ u, hsDiagFull D u ≤ e0 * (D.duS u : ℝ)) : MatK_at D η0 e0 := by

theorem matKF_of {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 : ℝ) (hC0 : 0 < C0) (lS : LinkS Fm C0)
    (cPr : ChosenProviso Fm C0) (lD : LinkDIV Fm Cabs CH) : MatKF Fm := by
```

Row 8.5 differs from `BlockReal_at`, `matK_at_of`, and `matKF_of`. First, `PMat D f u` has rows indexed by `D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)`, so `BlockReal_at` equates the matrix of `D.div.Bk u` at `v` only to the `Sum.inl` block (the target rows) of `(PMat D f u).map ε * Vr u` (with `IsIdOrConj ε`), not to the full matrix. Second, `matK_at_of` and `matKF_of` do not state the first two bounds for the matrices of the maps of 6.3 (`D.div.Bk u`), and instead, `MatK_at` (and `MatKF`) factors `Ball u = Bf u * Vr u` where `Ball u` matches `D.div.Bk u` on `Sum.inl` rows and states the two bounds for the first factors `Bf u`, which have `D.duS u` columns and `D.div.RR.ι ⊕ Fin (Dall - Drows)` rows. In addition, `LinkS` holds for `x ≥ x0` and requires `0 ≤ e0` without `-1 ≤ η0`, and `matKF_of` requires `0 < C0`, `ChosenProviso`, and `LinkDIV` (taking `max eta0 0` to obtain `-1 ≤ η0`).

Corrected row text replaces the table summary with the statement below.

> For large x, `LinkS` gives for every datum of a family numbers η0, η1, and √e0 at most exp(−x^(ε/8)) with 0 ≤ e0 such that `LinkS_at` holds. Under `ChProviso_at`, `LinkS_at` gives `hsSq` of `KD` at most (1 + η0)·`duS u`·`duS u′`/`Dstar` for distinct words, `hsDiagFull` at most e0·`duS u`, and `Dall` at most (1 + η1)·`Dstar`. `BlockReal_at` says that at one infinite place, in invertible frames, the matrix of the map `Bk u` equals the target-row `Sum.inl` block of `(PMat D f u).map ε` times an isometry `Vr u` for an `IsIdOrConj` map `ε`, and `blockReal_at_of` proves `BlockReal_at` from `BesselId`. `matK_at_of` proves `MatK_at` (which factors `Ball u = Bf u * Vr u`, matches `Bk u` on the target-row block of `Ball u`, and puts the two bounds on the first factors `Bf u` with weights `1/c0`) from `BlockReal_at`, positive `c0`, and the first two `LinkS_at` bounds, and `matKF_of` proves `MatKF` (adding −1 ≤ η0 and the exponential bounds) from `0 < C0`, `LinkS`, `ChosenProviso`, and `LinkDIV`.

### Row 10.1 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean` line 85, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShapeAlt.lean` lines 41-116, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ShapeOf.lean` lines 16-24, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 17-20, `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean` lines 16-18, `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean` lines 17-19, `src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean` lines 12-13, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` line 53, `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean` lines 102-105.

```lean
-- TopShape.lean line 85
theorem UpperTheory.Top.shape_closed_link_n_of_green : GlobalTheory.GLq.Green → _root_.GlobalTheory.Fc.TopShapeAlt True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG := by

-- TopShapeAlt.lean lines 41, 67, 101, 116
def TopShapeAlt (V NR : Prop) (N : FamClass → Prop) (G : Prop) : Prop :=
...
    (hVC : V)
...
    (nR : NR)
...
    G

-- ShapeOf.lean line 16
theorem GlobalTheory.Fc.goal_of_shape_of_hyps (V NR : Prop) (N : FamClass → Prop) (G : Prop) (t : _root_.GlobalTheory.Fc.TopShapeAlt V NR N G) (hV : V) (hR : NR) (h : _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition) : G :=

-- TopPlug.lean lines 17-20
theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)

-- ZeroFreeAllOfTopG.lean lines 16-18
def TopG : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) → FamilyClassConnected (G.cls la)

-- SupplyChi.lean lines 12-13
theorem UpperTheory.Top.supplyChi :
    ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req := by
```

Row 10.1 states that the families of data and the hosts are supplied by `shape_closed_link_n_of_green` and `supplyChi` from the premises of 1.4. Two aspects of the Lean statements differ from that description. First, `shape_closed_link_n_of_green` does not take `HypsAlt` as a premise, because its type maps `GlobalTheory.GLq.Green` into `TopShapeAlt True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG`, which quantifies over 53 separate hypotheses including two `True` parameters `hVC` and `nR`. In `zero_free_all_of_green_v_win`, a separate theorem `goal_of_shape_of_hyps` (called via `forall_goal_of_shape_of_hyps`) unpacks a `HypsAlt` record to fill 51 of those 53 hypotheses and passes `trivial` for `hVC` and `nR`. Second, `shape_closed_link_n_of_green` does not output families of data from `Green` and `HypsAlt` on their own, because it proves `TopG`, which itself takes `1 < la`, `HostExW la G.req`, and `HypV` on `G.cls la` as premises before yielding `FamilyClassConnected (G.cls la)` (the existence of a `ChainTied` family `Fm` of type `FamP eps` in `G.cls la`). Meanwhile `supplyChi` takes a primitive character `ψ` of type `PChar` and `VWinAt ψ 401` (rather than the uninstantiated `VWin`) and proves `HostExW (3 / 2) (GChi ψ).req`, which supplies `Ranks`, `Host R`, and a prime `q0` on `Scales (3 / 2)`.

Corrected row text replaces the table summary with the statement below.

> From `Green` and the 53 hypotheses of `TopShapeAlt` (with `True` in the slots `hVC` and `nR`), `shape_closed_link_n_of_green` proves `TopG`, which yields `FamilyClassConnected (G.cls la)` whenever `1 < la`, `HostExW la G.req`, and `HypV` on `G.cls la` hold. For each primitive character `ψ` of type `PChar`, `supplyChi` derives `HostExW (3 / 2) (GChi ψ).req` from `VWinAt ψ 401`, supplying `Ranks`, `Host R`, and a prime `q0` along scales `Scales (3 / 2)`. In `zero_free_all_of_green_v_win`, `forall_goal_of_shape_of_hyps` extracts 51 of the 53 hypotheses of `TopShapeAlt` from a record of type `HypsAlt` and passes `trivial` to `hVC` and `nR`.

### Row 10.2 (differs)

Lean source checked in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean` lines 17-18, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean` lines 15, 68-69, 95-116, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` lines 16-21 and 45-53, `src/Formalism/GaloisCohomology/Statement.lean` lines 79-82, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean` lines 8-10, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean` line 51, `src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean` line 10, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean` lines 73-77, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean` lines 35-104, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DefiniteSideCondition.lean` lines 40-50, `src/Formalism/LocalToGlobal/PtKOfReal.lean` lines 85-92.

```lean
-- LabelDatum.lean lines 15, 68-69, 112-116
abbrev Gn (g n : ℕ) : Type := GL (Fin n) (ZMod g)
def IsCusp {d : ℕ} (χ : Gn g d → ℂ) : Prop :=
  0 < d ∧ IsIrr χ ∧ ∀ a, 0 < a → a < d → res a (d - a) χ 1 1 = 0
def Green : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (d : ℕ), 0 < d → ∃ τ : (ZMod g)[X] → Gn g d → ℂ,
    (∀ P, IsPrimeLab d P → IsCuspOf L P (τ P) ∧ τ P 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1)) ∧
    (∀ P P', IsPrimeLab d P → IsPrimeLab d P' → τ P = τ P' → P = P') ∧
    ∀ χ : Gn g d → ℂ, IsCusp χ → ∃ P, IsPrimeLab d P ∧ χ = τ P

-- ExistsPageN.lean lines 16-21, 53
def VVle (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData E Ω p),
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → Formalism.GaloisCohomology.shaLen (ld p) (e : ℤ) ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes,
      ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@Formalism.GaloisCohomology.shaLen E Ω _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) (e : ℤ)).toNat : ℝ) ≤ B
def VWin : Prop := ∀ ψ : PChar, VWinAt ψ 401

-- VwinOfRow.lean lines 8-10
theorem UpperTheory.One.vwin_of_row (h : UpperTheory.V.Z.Win.RowT) : UpperTheory.Top.VWin :=

-- WeakOfAtt.lean line 51
def RowT : Prop := UpperTheory.GalStar.Row0b fun h rc => IsRecT h rc

-- RecT.lean line 10
def UpperTheory.One.M.Row : Prop := UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc

-- WeightsConjBis.lean lines 73-77
def Row0b : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), PropsB Rc π ι r wt HT

-- Hyps.lean lines 35-38, 77, 103
structure HypsAlt (N : FamClass → Prop) (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) : Type 1 where
  𝒜 : FamClass
  σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜
  cT : ℝ → ℝ → ℝ
...
  rRows : _root_.GlobalTheory.Fc.R1.SelectionDefiniteRows DR 𝒜 σ
...
  nRest : N (D3 3 𝒜)

-- PtKOfReal.lean lines 85, 92
def RowsU [_root_.NumberField.IsTotallyComplex D.what₂.LL] {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields} ... : Prop :=
  ∃ (ch : ColChain (c.face Pk.Zs) w) (T : ChainTie ch (c.memQ w)), FirstCols c.hE T ∧
```

Row 10.2 differs from the Lean declarations in four respects. First, `GlobalTheory.GLq.Green` does not parametrise all characters of arbitrary finite general linear groups, because it restricts both the group to `GL (Fin d) (ZMod g)` for a prime `g` and the characters to cuspidal irreducible characters satisfying `IsCusp`, parametrising them via `IsPrimeLab d` polynomials over `ZMod g` relative to a `LabelDatum g` with explicit `IsCuspOf` values and `τ P 1` dimension formula. Second, `vwin_of_row` takes a premise of type `UpperTheory.V.Z.Win.RowT` (defined in `WeakOfAtt.lean`), not an identifier named `Row`, and `WeightsConjBis.lean` defines `UpperTheory.GalStar.Row0b` (parameterized by `Rc` of type `RecNotion`) rather than `Row`. The declaration named `Row` for Galois representations is `UpperTheory.One.M.Row` in `RecT.lean`, which unfolds to the same proposition `UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc` as `RowT`, while bare `Row` also names at least nine unrelated declarations in `src/`. Third, `Row0b` specialized to `IsRecT` does not assert general existence of Galois representations, because it quantifies over CM fields `E`, primes `l`, `ι` of type `Qbar l ≃+* ℂ`, `1 ≤ a`, and regular algebraic polarized cuspidal representations `π` of type `CuspSub E a`, asserting `r`, `wt`, and `HT` satisfying `PropsB`. Fourth, `HypsAlt` is a 46-field `Type 1` structure consisting of a family class `𝒜`, a selection `σ` of type `RawSel BundleCondition 𝒜`, two functions `cT` and `c30`, a real constant `cIc`, and 41 proposition-valued fields, and it does not store `ColChain` or `ChainTie` fields directly. Instead, `σ` provides `BundleCondition` data (`RecTAlt`, `STiesRAlt`, `RowSideFamily`, `SquareIntegrableColumns`, and `RealTBAlt`), while the field `rRows` takes the parameter `DR` (instantiated to `DefiniteSideCondition` in `zero_free_all_of_green_v_win`), which asserts `RowsU`, the existential proposition that a `ColChain` and `ChainTie` exist for each word. Also `VWin` specifically bounds `shaLen` (for `Sha` classes in `H1` vanishing above `l`) weighted by `log l` over twists `1 ≤ e < ⌊x ^ 401⌋₊` by `√(exp (x ^ eps))` for `IsChiField` subfields of cyclotomic fields on `[Y, Y ^ 2]` windows, and the third premise of `zero_free_all_of_green_v_win` is `Nonempty` of `HypsAlt` instantiated with `fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm` and `DefiniteSideCondition`.

Corrected row text replaces the table summary with the statement below.

> The premises of `zero_free_all_of_green_v_win` are `Green`, `VWin`, and `Nonempty` of `HypsAlt` instantiated with `fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm` and `DefiniteSideCondition`. `Green` states that for every prime `g`, `LabelDatum g`, and `d > 0`, a map `τ` bijects `IsPrimeLab d` polynomials over `ZMod g` onto cuspidal irreducible characters `IsCusp` of `GL (Fin d) (ZMod g)` with `IsCuspOf` character values and the `τ P 1` product formula. `VWin` states that for every primitive character `ψ`, small `eps`, and `e` satisfying `PageN`, on `[Y, Y ^ 2]` windows for primes `q` and `d` satisfying `WinPair`, every `IsChiField` number field `E` has finite `shaLen` for `1 ≤ e < ⌊x ^ 401⌋₊` and `log l`-weighted sum of `shaLen` at most `√(exp (x ^ eps))`. `vwin_of_row` derives `VWin` from `UpperTheory.V.Z.Win.RowT` (definitionally equal to `UpperTheory.One.M.Row` and `Row0b` applied to `IsRecT`), which states that for every CM field `E`, prime `l`, isomorphism `Qbar l ≃+* ℂ`, `1 ≤ a`, and regular algebraic polarized cuspidal representation `π`, there exist `r`, `wt`, and `HT` satisfying `PropsB`. `HypsAlt` is a 46-field record holding a family class `𝒜`, a `RawSel BundleCondition 𝒜` selection `σ`, functions `cT` and `c30`, a real `cIc`, and 41 hypotheses including `rRows`, which under `DefiniteSideCondition` yields `RowsU`, asserting that `ColChain` and `ChainTie` witnesses exist for each word.

### Contradicted entries in the lists under the tables

Five entries in the reading lists under the tables of `CLAIMS.md` are contradicted by the Lean text.

#### List entry 1 (Step 5, two bounds on one slope)

Lean source checked in `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 109-114.

The quoted list entry in `CLAIMS.md` reads as shown below.

> The report of one reading names no source for the eleventh of the eleven conditions, `HidaSetting`, which is a list of sign conditions.

```lean
def HidaSetting : Prop :=
  0 < D.x ∧ 0 < D.b ∧ 0 ≤ D.a ∧ 0 ≤ D.b' ∧ 0 < D.k ∧ 0 < D.v ∧ 0 < f ∧
  (∀ t, 0 ≤ D.aT t) ∧ (∀ u0 j ρ, 0 < D.w u0 j ρ) ∧
  (∀ u0 (u : W u0), 0 < D.d u0 u) ∧ (∀ u0 (u : W u0), 0 < D.T u0 u) ∧
  (∀ u0 (u : W u0), D.muN u0 u ≤ D.muMaxN u0 u) ∧
  0 ≤ C.cSl1 ∧ D.delBar < 1 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧ D.eBar ≤ 1 / 4
```

`HidaSetting` is not merely a list of sign conditions, because three of its seventeen conjuncts are comparison and upper bounds (`D.muN u0 u ≤ D.muMaxN u0 u`, `D.delBar < 1`, and `D.eBar ≤ 1 / 4`).

A corrected entry replaces it with the statement below.

> The report of one reading names no source for the eleventh of the eleven conditions, `HidaSetting`, which is a conjunction of fourteen positivity or nonnegativity conditions together with `D.muN u0 u ≤ D.muMaxN u0 u`, `D.delBar < 1`, and `D.eBar ≤ 1 / 4`.

#### List entry 2 (Step 9, the exponent 1/2)

Lean source checked in `src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` lines 121-124 and `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` lines 430-445.

The quoted list entry in `CLAIMS.md` reads as shown below.

> The inequality that the proof divides has two further small terms, a term 2·nT·m·b/x on the side of the error and a lowering of the prime sum by 4·x^(1/2 + ε), and both are absorbed in the exponent.

```lean
def GrowthSizeBound : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)

  set G : ℝ := GmA D ell Kp c x - SigA D ell A0 Kp x with hG
```

In `GrowthSizeBound`, the quantity lowered by `4 * x ^ (1 / 2 + ε)` is an arbitrary real number `Gx`, and in `ch_core` it is `GmA D ell Kp c x - SigA D ell A0 Kp x` (a weighted real-part sum including `ell ψ` and `Gz` minus `SigA`), not a prime sum.

A corrected entry replaces it with the statement below.

> The inequality that the proof divides has two further small terms, a term `2 * nT * m * b / x` on the side of the error and a lowering of the real quantity `Gx` (instantiated as `GmA D ell Kp c x - SigA D ell A0 Kp x` in `ch_core`) by `4 * x ^ (1 / 2 + ε)`, and both are absorbed in the exponent.

#### List entry 3 (Added by the readings under Step 7)

Lean source checked in `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean` lines 251-282 and 291-319, and `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean` lines 120-169 and 258-299.

The quoted list entry in `CLAIMS.md` reads as shown below.

> The proof of 7.3 pairs each lower row of the lift with a row under the hook product and leaves the top row without a partner. This comes from one reading of the proof.

```lean
    have hν : phRows ((Finset.univ.val.map fun i => w + c i) + blk) =
        ∑ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) + ph ((w + c (Fin.last n) : ℕ) : ℝ) +
          phRows blk := by
    have hpair : ∀ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) - ph ((r i : ℕ) : ℝ) ≤
        ((c i.castSucc : ℝ) - c' i) * Real.log A + sh * Real.log A := by
  refine ⟨fun i => νr i.castSucc.succ - wr, fun i => ar i - (wr + T), ar, νr (Fin.last (n + 1)), blk, sm,
    ⟨?_, ?_⟩, ?_, Hl, hB, ?_, rfl⟩
    have hfa2 : ∑ i : Fin (n + 1), ph ((r i : ℕ) : ℝ) =
        ph ((r 0 : ℕ) : ℝ) + ∑ i : Fin n, ph ((r i.succ : ℕ) : ℝ) := Fin.sum_univ_succ _
    have hpair : ∀ i : Fin n, ph ((w + c i : ℕ) : ℝ) - ph ((r i.succ : ℕ) : ℝ) ≤
        ((c i : ℝ) - c' i.succ) * Real.log A + sh * Real.log A := by
```

In young_diagram_factorial, the non-top branch IsRowsOff uses Fin.sum_univ_castSucc to separate the last main row w plus c (Fin.last n) and pairs rows 0 to n minus 1, including the top row, with r i. Meanwhile top_core and the IsRowsTop branch separate both the top row aT plus w and the bottom main row r0 at Fin.last (n plus 1), pair only the n equals k minus 2 middle rows with r i.succ, and bound aT plus w, r0, and r 0 together outside hpair.

A corrected entry replaces it with the statement below.

> In the proof via young_diagram_factorial, non-top places IsRowsOff pair the first k minus 1 rows including the top row with rows under the hook product and leave the bottom main row without a partner, while top places IsRowsTop pair only the k minus 2 middle rows with r i.succ and bound both the top row and the bottom main row separately alongside r 0.

#### List entry 4 (Step 8, the lower bound)

Lean source checked in `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 38, 80-81, 197, and 202.

The quoted list entry in `CLAIMS.md` reads as shown below.

> The reading of 8.2 is an interpretation. The second bound says that each map is an isometry up to a small relative error after scaling. For one pair of words the first bound is 1 + η0 times the mean value for two random subspaces of the dimensions of the two words in a space of dimension `Dstar`, and by the upper side of the first condition of 8.4 it is a small share of the dimension of a word when Γ is large.

```lean
  (∀ i, hsSq (KdG B ga i - 1) ≤ e0 * (Fintype.card (ι i) : ℝ)) ∧
...
  (∀ i (k : κ) (j : ι i),
    Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)
...
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
...
    InputSG Bf γ Dstar η0 η1 e0 →
```

The Lean text in `InputSG` and `JointARam` directly contradicts calling the second bound a statement about each map `B i`. `InputSG` bounds `hsSq (KdG Bf γ i - 1)` on the first factors `Bf i` of `Ball i = Bf i * Vr i`, where `Ball i` agrees with `B i` only on the target rows `Sum.inl k` and may have extra rows `κ₁` and fewer columns `ι i` than `ιf i`. Even after compression by `Vr i`, `FrameDeviationLinear` on `Ball` is a sum across all `i` rather than a per-map bound on `B i`. Note that comparing the first bound to two random subspaces of dimensions `duS u` and `duS u'` is an interpretation going beyond the Lean code.

A corrected entry replaces it with the statement below.

> The reading of 8.2 is an interpretation. The second bound of `InputSG` applies to each extended first factor `Bf i` (with extra rows `κ₁` and extra columns `ιf i` via `Ball i = Bf i * Vr i`), rather than to the map `B i` itself, and after compression by `Vr i`, `FrameDeviationLinear` on `Ball` bounds a sum over the family. For one pair of words the first bound of `InputSG` is 1 + η0 times `|ιf i|·|ιf j| / Dstar`, which by the upper side of `ChProviso_at` is at most (1 + η0)·C0·`duS u`/Γ² in the datum application.

#### List entry 5 (Step 8, the lower bound)

Lean source checked in `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 31-32, 39, and 198-202.

The quoted list entry in `CLAIMS.md` reads as shown below.

> The columns of all words outnumber the rows at least 19 times, so the images of the maps overlap, and by the reading the first bound says that they overlap as random subspaces do.

```lean
def RsG {I : Type} [Fintype I] (ι : I → Type) [∀ i, Fintype (ι i)] : ℝ :=
  ∑ i, (Fintype.card (ι i) : ℝ)
...
  (Fintype.card α : ℝ) ≤ (1 + η1) * Dstar
...
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
```

The Lean hypotheses in `JointARam` guarantee `RsG ιf ≥ (800 / 41) * Fintype.card (κ ⊕ κ₁) > 19 * Fintype.card (κ ⊕ κ₁)` for the first-factor columns `ιf`, whereas the columns `ι` of the maps `B i` and lattices `N i` satisfy `∑ i, (|ιf i| - |ι i|) ≤ de * RsG ιf` with `de ≤ 1 / 4`, which only guarantees `(3 / 4) * (800 / 41) = 600 / 41` (about `14.63`) times `Fintype.card (κ ⊕ κ₁)`. In addition, the bound on `Fintype.card α` in `InputSG` counts all rows `κ ⊕ κ₁`, not only the target rows `κ`. Note that interpreting the first bound as overlap like random subspaces goes beyond the Lean text.

A corrected entry replaces it with the statement below.

> The columns of all first factors `Bf` outnumber all rows `κ ⊕ κ₁` at least 19 times (since `RsG ιf ≥ Dstar / sg` with `sg ≤ 1 / 20` and `|κ ⊕ κ₁| ≤ (1 + η1) * Dstar` with `η1 ≤ sg / 2` gives at least 800/41 times the rows), whereas the columns of the word lattices `Nu u` (`∑ |ι i|`) only satisfy `∑ (|ιf i| - |ι i|) ≤ de * RsG ιf`, which in `JointARam` (`de ≤ 1 / 4`) guarantees at least 600/41 times `|κ ⊕ κ₁|`. An interpretation that the images overlap as random subspaces do goes beyond the Lean text.

## Part C, findings on the commentary

The independent calculation check of the four division terms from `errorBracketSizeWindows`, `RestSize`, `BNBounds`, and the hypotheses of `ch_core` is given first, followed by twenty findings on the four assigned commentary sections of `README.md`.

### Independent check of the error-bracket division

We expand `errorBracketSizeWindows x ε n nT nT2 m b k aE` from `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean` lines 75-77 as the sum of four terms `T1 = nT * aE`, `T2 = nT * aE * (m ^ 2 / k)`, `T3 = m * (2 * n * m * b * x ^ ε)`, and `T4 = m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))`. From `BNBounds` in `src/Formalism/SizeWindowBrackets/SChain.lean` lines 37-40, `Dd.B0 ≤ 2 * n * m * b * x ^ ε` and `Dd.Nc ≤ nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))` (with `n = Fintype.card H` and `nT2 = T2.card`), which match the two inner terms `B = 2 * n * m * b * x ^ ε` and `N = nT2 * k * b * x ^ (2 * ε) / n ^ 2` (since `x ^ ε / x ^ (-ε) = x ^ (2 * ε)` for `0 < x`). From `RestSize` (`SChain.lean` lines 57-62), we have `aE ≤ 2 * x * b`, `x ^ (-(ε / 8)) * n / 2 ≤ nT` (so `n / nT ≤ 2 * x ^ (ε / 8)`), `x ^ (-ε) ≤ nT2 / n`, `x ^ (1 / 2 - ε) ≤ m`, and `k ≤ n ^ 2 * x ^ (1 / 2 - ε)`. From `ch_core` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` lines 347-374), we also have `0 ≤ C`, `0 < ε`, `3 ≤ x` (so `1 ≤ x` and `0 < x`), `26 ≤ x ^ (3 * ε / 8)`, `0 < n`, `0 < b`, `0 ≤ aE`, `0 < k`, `m ≤ x ^ (1 / 2 + ε / 2)`, `x * m ≤ k`, and `nT2 ≤ n`, which also force `0 < nT` and `0 < m`. Dividing each of the four terms by `nT * m * b` gives the following bounds. First, `T1 / (nT * m * b) = aE / (m * b) ≤ (2 * x * b) / (m * b) = 2 * x / m`, and `x ^ (1 / 2 - ε) ≤ m` gives `2 * x / m ≤ 2 * x / x ^ (1 / 2 - ε) = 2 * x ^ (1 / 2 + ε) ≤ 2 * x ^ (1 / 2 + 13 * ε / 8)`. Second, `T2 / (nT * m * b) = aE * m / (k * b) ≤ (2 * x * b * m) / (k * b) = 2 * (x * m / k) ≤ 2` since `x * m ≤ k`, and `1 ≤ x ^ (1 / 2 + 13 * ε / 8)` gives `2 ≤ 2 * x ^ (1 / 2 + 13 * ε / 8)`. Third, `T3 / (nT * m * b) = 2 * n * m * x ^ ε / nT ≤ 2 * (2 * x ^ (ε / 8)) * m * x ^ ε = 4 * m * x ^ (9 * ε / 8)`, and `m ≤ x ^ (1 / 2 + ε / 2)` gives `4 * m * x ^ (9 * ε / 8) ≤ 4 * x ^ (1 / 2 + 13 * ε / 8)`. Fourth, `T4 / (nT * m * b) = nT2 * k * x ^ (2 * ε) / (n ^ 2 * nT) = (nT2 / n) * (k / n ^ 2) * (n / nT) * x ^ (2 * ε) ≤ 1 * x ^ (1 / 2 - ε) * (2 * x ^ (ε / 8)) * x ^ (2 * ε) = 2 * x ^ (1 / 2 + 9 * ε / 8) ≤ 2 * x ^ (1 / 2 + 13 * ε / 8)`. Summing all four terms yields `(T1 + T2 + T3 + T4) / (nT * m * b) ≤ (2 + 2 + 4 + 2) * x ^ (1 / 2 + 13 * ε / 8) = 10 * x ^ (1 / 2 + 13 * ε / 8)`, so `Err / (nT * m * b) ≤ 10 * x ^ (C * ε) * x ^ (1 / 2 + 13 * ε / 8)`. In `GrowthSizeBound` (`src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` lines 121-124), dividing `(nT * m * b) * ((nT2 / n) / 2) * (Gx - 4 * x ^ (1 / 2 + ε)) ≤ Err + 2 * nT * m * b / x` by `nT * m * b` turns the additional error term `2 * nT * m * b / x` into `2 / x ≤ 1 ≤ x ^ (C * ε) * x ^ (1 / 2 + 13 * ε / 8)`, giving `((nT2 / n) / 2) * (Gx - 4 * x ^ (1 / 2 + ε)) ≤ 11 * x ^ (C * ε) * x ^ (1 / 2 + 13 * ε / 8)`. Dividing by `(nT2 / n) / 2` where `nT2 / n ≥ x ^ (-ε)` multiplies the right side by at most `2 * x ^ ε` (turning `2 / x` into at most `4 * x ^ ε / x`, and `11` into `22`), giving `Gx - 4 * x ^ (1 / 2 + ε) ≤ 22 * x ^ (1 / 2 + (C + 13 / 8 + 1) * ε) = 22 * x ^ (1 / 2 + (C + 21 / 8) * ε)`. Adding `4 * x ^ (1 / 2 + ε) ≤ 4 * x ^ (1 / 2 + (C + 21 / 8) * ε)` yields `Gx ≤ 26 * x ^ (1 / 2 + (C + 21 / 8) * ε)`, and `26 ≤ x ^ (3 * ε / 8)` gives `Gx ≤ x ^ (1 / 2 + (C + 13 / 8 + 1 + 3 / 8) * ε) = x ^ (1 / 2 + (C + 3) * ε)`. Thus every intermediate term, factor, and exponent arithmetic step in `README.md` lines 621-641 is verified. As a note on the Lean formalization in `proposition_size_bound` (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean` lines 242-327), Lean does not write literal division by `nT * m * b` or by `(nT2 / n) / 2`, instead factoring `nT * m * b` out of the upper bound via `SZ.T1` through `SZ.T4`, cancelling `nT * m * b` with `le_of_mul_le_mul_left`, multiplying by `2`, and using `1 ≤ x ^ ε * (nT2 / n)`.

### Twenty findings on the assigned sections of `README.md`

#### Finding 1 (The Landau step)

The quoted sentence in `verification/strategy/README.md` reads as shown below.

> In the first a zero ρ at height τ is the singularity nearest to σ + iτ, at a distance d below σ − θ, and the integral at σ + iτ has norm about c/d^k.

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauNearest.lean` lines 40-78, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean` lines 96-137, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauPoleAsym.lean` lines 23-28.

```lean
theorem landau_nearest {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ D : ℝ}
    (hle : ∀ ρ ∈ Z, ρ.re < σ) (hD : D < σ) {ρ₁ : ℂ} (h₁ : ρ₁ ∈ Z) (hρ₁ : σ - ρ₁.re < D) :
    ∃ γ : ℝ, ∃ ρ ∈ Z, ∃ r : ℝ, ‖(σ : ℂ) + γ * I - ρ‖ < r ∧ r ≤ D ∧
      ∀ w ∈ Z, w ∈ Metric.ball ((σ : ℂ) + γ * I) r → w = ρ := by
...
  set B : Set ℝ := (fun p : ℂ × ℂ =>
      ((σ - p.1.re) ^ 2 + p.1.im ^ 2 - (σ - p.2.re) ^ 2 - p.2.im ^ 2) / (2 * (p.1.im - p.2.im))) ''
      (F ×ˢ F) with hB
  have hBfin : B.Finite := (hF.prod hF).image _
  obtain ⟨γ, hγI, hγB⟩ := ((Set.Ioo_infinite (show ρ₁.im - ε < ρ₁.im + ε by linarith)).diff hBfin).nonempty
...
  obtain ⟨ρ, hρF, hmin⟩ := Set.exists_min_image F (fun w => ‖c - w‖) hF ⟨ρ₁, hρ₁F⟩

-- landauWindow.lean lines 96-98, 117, 126-127, 133-137
  · obtain ⟨γ, ρ, hρ, r, hr1, hr2, huniq⟩ := landau_nearest hP.iso hle (by linarith : D < σ) h₁ hρ₁
    obtain ⟨c, hc, -, hp⟩ := hP.pole ρ hρ
    set z : ℂ := (σ : ℂ) + γ * I with hz
...
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (d + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
...
    have h4 : ‖c / (z - ρ) ^ (k + 1)‖ = ‖c‖ / d / d ^ k := by
      rw [norm_div, norm_pow, pow_succ', div_div]
...
    have h7 := norm_sub_norm_le (c / (z - ρ) ^ (k + 1))
      ((-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ))
    rw [norm_sub_rev] at h7
    rw [add_div]
    linarith
```

In landau_nearest, the height γ (written τ in the commentary) is chosen in an interval around ρ₁.im avoiding the finite set B of heights that are equidistant from two zeros in F, and ρ is then chosen to minimize the distance to σ + γ * I. Consequently, ρ does not in general lie at height τ. In addition, landau_pole_asym approximates the normalized Taylor coefficient (-1)^k * iteratedDeriv k Φ z / k! by c / (z - ρ) ^ (k + 1), so in landau_window the pole term has norm (‖c‖ / d) / d ^ k rather than c / d ^ k, and the integral at σ + iγ is bounded below by (‖c‖ / d) / d ^ k - M / e ^ k.

A corrected sentence replaces it with the statement below.

> In the first case `landau_nearest` chooses a height τ avoiding equidistant ties so that a unique zero ρ is the singularity nearest to σ + iτ at a distance d below σ − θ, and the pole term of the integral at σ + iτ has norm (‖c‖/d)/d^k up to an error of at most M/e^k.

#### Finding 2 (The Landau step)

The quoted sentence in `verification/strategy/README.md` lines 310-317 reads as shown below.

> In the second case the nearest singularity of σ is a real zero at a distance d below σ − θ, and its positive residue makes the integral at σ about c/d^k, while the norm at σ + iτ is at least 0.

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean` lines 157-170, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauPoleAsym.lean` lines 23-28.

```lean
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (σ - β + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    refine landau_window_contra (c := c.re / (σ - β)) (d := σ - β) (e := (σ - β + r) / 2) (E := σ - θ)
      (M := M) (C := C) (div_pos hc1 hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_
    obtain ⟨U, hU, k, hk, hb⟩ := hkey η hη U₀
    refine ⟨U, hU, k, hk, ?_⟩
    have h1 := hb 0
    have h2 := hM k
    have h4 : (c / ((σ : ℂ) - β) ^ (k + 1)).re = c.re / (σ - β) / (σ - β) ^ k := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.div_ofReal_re, pow_succ', div_div]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ) - c / ((σ : ℂ) - β) ^ (k + 1)))).1
    rw [Complex.sub_re, h4] at h6
    have h7 := norm_nonneg ((-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + (0 : ℝ) * I) / (k.factorial : ℂ))
    linarith
```

In the second case of landau_window, the positive real residue c contributes (c / (σ - β) ^ (k + 1)).re = (c.re / d) / d ^ k where d = σ - β, rather than c / d ^ k, and landau_pole_asym at σ bounds the regular part error by M / e ^ k. Furthermore, landau_window instantiates the height parameter of landau_window_key at 0 via hb 0, so it uses the nonnegativity of the norm at σ itself rather than at a nonzero height σ + iτ.

A corrected sentence replaces it with the statement below.

> In the second case the nearest singularity of σ is a real zero β at distance d = σ − β below σ − θ, and its positive residue c makes the pole term at σ equal to (c/d)/d^k up to an error of at most M/e^k, while the norm term in the key bound evaluated at height 0 is nonnegative.

#### Finding 3 (The Landau step)

The quoted sentence in `verification/strategy/README.md` line 312 reads as shown below.

> In both cases c/d^k is at most M/e^k plus a multiple of e^(ηU)/(σ − θ)^k, with d below e and e at most σ − θ.

Lean source checked in `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean` lines 117-120, 157-159.

```lean
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (d + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    obtain ⟨M', hM'⟩ := landau_cauchy (r' := (d + r) / 2) hdiff' (by linarith) (by linarith)
    refine landau_window_contra (c := ‖c‖ / d) (d := d) (e := (d + r) / 2) (E := σ - θ) (M := M + M') (C := C)
      (div_pos (norm_pos_iff.2 hc) hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_
...
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (σ - β + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    refine landau_window_contra (c := c.re / (σ - β)) (d := σ - β) (e := (σ - β + r) / 2) (E := σ - θ)
      (M := M) (C := C) (div_pos hc1 hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_
```

Because c in the preceding sentences denotes the residue, the left side passed to landau_window_contra in landau_window is (‖c‖ / d) / d ^ k in the first case and (c.re / d) / d ^ k in the second case rather than c / d ^ k. Also, the numerator M in the first case is the sum M + M' from landau_pole_asym at σ + iγ and landau_cauchy at σ, whereas in the second case it is M from landau_pole_asym at σ, and in both cases e is strictly below σ - θ.

A corrected sentence replaces it with the statement below.

> In both cases the pole term (‖c‖/d)/d^k or (c/d)/d^k is at most a combined remainder bound M_tot/e^k plus a multiple of e^(ηU)/(σ − θ)^k, with d < e < σ − θ.

#### Finding 4 (The pair of primes)

The quoted sentence in `verification/strategy/README.md` lines 506-512 reads as shown below.

> Inside the block the proof bounds |`S`|² at any y by twice |`S`|² at V plus 2V times the integral of the square of the derivative of `S` in y.

Lean source checked in `src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean` lines 66-67 and lines 122-124.

```lean
private theorem bs_hasDeriv_S (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) (x : ℝ) :
    HasDerivWithinAt (fun y => S Z y q κ) (bsD Z x q κ) (Set.Ioi x) x := by

private theorem bs_normSq_S_le (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) {Y W y : ℝ} (hW : W ≤ 2 * Y)
    (hY : 0 ≤ Y) (hy : y ∈ Set.Icc Y W) :
    ‖S Z y q κ‖ ^ 2 ≤ 2 * ‖S Z Y q κ‖ ^ 2 + 2 * Y * ∫ v in Y..W, ‖bsD Z v q κ‖ ^ 2 := by
```

Because `min 1 (y / m)` has corners at integers `m`, `bs_hasDeriv_S` proves that `bsD` is the right-hand derivative of `S` (`HasDerivWithinAt` on `Set.Ioi x`), and `bs_normSq_S_le` bounds `‖S Z y q κ‖ ^ 2` using the integral of `‖bsD Z v q κ‖ ^ 2` over the whole block `[V, W]` rather than only `[V, y]`.

A corrected sentence replaces it with the statement below.

> Inside a block `[V, W]` with `W ≤ 2·V`, the proof bounds `‖S‖²` at any `y` by twice `‖S‖²` at `V` plus `2·V` times the integral over `[V, W]` of the square of the right-hand derivative `bsD` of `S` in `y`.

#### Finding 5 (The pair of primes)

The quoted sentence in `verification/strategy/README.md` line 518 reads as shown below.

> The sum of |`S`|² over p becomes a sum over pairs n, n′ of the coefficients times the sum of (n/p)·(n′/p) over p.

Lean source checked in `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainA.lean` lines 13-16, `src/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean` line 23.

```lean
theorem meansq_expand (PP I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ)
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (J : ℕ → ℕ → ℤ) :
    (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by

  have hexp := meansq_expand P (Icc 1 N) (cN y) hc0 κ hκ (fun n q => jacobiSym (n : ℤ) q)
```

Expanding `‖S‖²` preserves the factors `κ n * starRingEnd ℂ (κ n')` inside each `(n, n')` term, and `meansq_expand` uses `‖κ n‖ ≤ 1` and the triangle inequality to obtain an upper bound (`≤`) with the absolute value `|∑ q ∈ PP, (n/q)·(n'/q)|` rather than an equality without `κ` or absolute values.

A corrected sentence replaces it with the statement below.

> Using `‖κ n‖ ≤ 1` and the triangle inequality, `meansq_expand` bounds the sum of `‖S‖²` over `p` from above by the sum over pairs `n, n′` of the coefficients `cN y n · cN y n′` times the absolute value of the sum of `(n/p)·(n′/p)` over `p`.

#### Finding 6 (The pair of primes)

The quoted sentence in `verification/strategy/README.md` line 528 reads as shown below.

> It states for all exponents A′ and B′ and every large Y that each odd squarefree r > 1 that is coprime to m₀ and at most Y^(A′), with one possible exception, has a sum of (p/r) over the primes p of `PPset` of at most Y^(−B′) times their number.

Lean source checked in `src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean` lines 158-161.

```lean
theorem twistK :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m₀ a₀ : ℕ), admitted ε Y U m₀ a₀ →
      ∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → (s : ℝ) ≤ Y ^ A → s ≠ nstar →
        |∑ q ∈ PPset m₀ a₀ U, (jacobiSym (q : ℤ) s : ℝ)| ≤ Y ^ (-B) * ((PPset m₀ a₀ U).card : ℝ) := by
```

`twistK` requires `0 < ε`, `0 < A`, `0 < B`, and `admitted ε Y U m₀ a₀`, and its conclusion bounds the absolute value `|∑ q ∈ PPset m₀ a₀ U, (jacobiSym (q : ℤ) s : ℝ)|` rather than only the sum without absolute values.

A corrected sentence replaces it with the statement below.

> It states for `0 < ε`, all positive exponents `A′` and `B′`, every large `Y`, and `admitted ε Y U m₀ a₀` that each odd squarefree `r > 1` coprime to `m₀` and at most `Y^A′`, with one possible exception, has a sum of `(p/r)` over the primes `p` of `PPset` of absolute value at most `Y^(−B′)` times their number.

#### Finding 7 (From the two bounds on the slope to the exponent 1/2)

The quoted sentence in `verification/strategy/README.md` lines 652-659 reads as shown below.

> The conditions of the next subsection then require that errors of one lift stay within a constant times `B0`. The condition `EComp5` is one of them.

Lean source checked in `src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean` lines 28-29 and `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean` lines 92-92, 116-124.

```lean
def Ee (u0 : U0) (u : W u0) : ℝ := ∑ j, D.EeJ u0 u j

def DIV : Prop :=
  ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u)))
      + C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)

def EComp5 : Prop :=
  ∀ u0 (u : W u0), |D.Ee u0 u - (m : ℝ) * D.sumA * D.lg| ≤ C.cE * (m : ℝ) * D.B0
```

In `SizeData₂`, `EComp5` bounds `|D.Ee u0 u - m * D.sumA * D.lg|` by `C.cE * m * D.B0`, where `D.Ee u0 u` is the sum `∑ j, D.EeJ u0 u j` over all `m` lifts, and `DIV`, `HComp`, and `QuotientSlopeBoundsWith` similarly carry `m * D.B0` rather than bounding one lift by a constant times `B0`.

A corrected sentence replaces it with the statement below.

> The conditions of the next subsection then bound sums over all `m` lifts (such as `D.Ee u0 u = ∑ j, D.EeJ u0 u j` in `EComp5`, and similarly `DIV`, `HComp`, and `QuotientSlopeBoundsWith`) within constants times `m * D.B0`.

#### Finding 8 (From the two bounds on the slope to the exponent 1/2)

The quoted sentence in `verification/strategy/README.md` lines 692-698 reads as shown below.

> The mean of `DIV` over u, taken with the weights of `SlopeIneq`, and `SlopeIneq` together cancel `muCC` and the mean of `h` and leave an upper bound for the mean of `muN`.

Lean source checked in `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean` lines 46-62, 109-156.

```lean
lemma s_lower5 (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.Ga u0 + D.muCC u0 - K5v5 D C u0 - wmean (D.d u0) (Lo5 D C Xpp u0) ≤ D.s u0
```

In `LevelOfCongruence.lean`, the proof never takes the mean of `DIV` to isolate an upper bound for the mean of `muN` alone. Instead, `s_lower5` bounds `D.s u0` (the `D.d u0`-weighted mean of `D.muN u0 u - D.h u0 u`) from below, and `Ga_bound5` combines that lower bound with `SlopeIneq` to cancel `D.s u0` and `D.muCC u0` and bound `D.Ga u0` from above.

A corrected sentence replaces it with the statement below.

> In the Lean proof, `s_lower5` combines `DIV`, `QuotientSlopeBoundsWith`, `Count5`, `EComp5`, `Slopes`, and `HidaSetting` to cancel `h u` pointwise and bound `D.s u0` (the weighted mean of `muN - h`) from below, and `Ga_bound5` combines that lower bound on `D.s u0` with `SlopeIneq` (plus `HComp`, `HHBound`, and `FParams`) to cancel `D.s u0` and `D.muCC u0` and bound `D.Ga u0` from above.

#### Finding 9 (From the two bounds on the slope to the exponent 1/2)

The quoted sentence in `verification/strategy/README.md` lines 707-714 reads as shown below.

> By this session's own algebra the lower bound of `Count5` for log `T u` turns the main term of `DIV` into `Main` minus m times the sum of the `aT t` times `lg`, plus an error.

Lean source checked in `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean` lines 101-107 and `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean` lines 131-178.

```lean
lemma key_identity5 (hv : 0 < D.v) (hf : 0 < f) (u0 : U0) (hw : ∀ j ρ, 0 < D.w u0 j ρ) :
    D.SDiv - D.sumA * Lam5 D C u0 + (m : ℝ) * D.sumA * D.lg =
      D.Main u0 + D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) := by
  have h := D.key_identity C hv hf u0 hw
  unfold Data.abelian₂ at h
  unfold Lam5
  linear_combination h
```

This algebraic rewrite is proved inside Lean by `Data.key_identity` and `key_identity5`, which `Ga_bound5` invokes directly, rather than being only an external calculation by the session.

A corrected sentence replaces it with the statement below.

> By `Data.key_identity` and `key_identity5` in the Lean code, the lower bound of `Count5` for `Real.log (D.T u0 u)` turns the main term of `DIV` into `D.Main u0 - m * D.sumA * D.lg` plus `D.sumA * (C.cCount * (D.La + m ^ 2 * D.La / D.k))`.

#### Finding 10 (From the two bounds on the slope to the exponent 1/2)

The quoted sentence in `verification/strategy/README.md` line 711 reads as shown below.

> The tie `TieArith` gives the number w of the record as the number `wj` of the datum, which is the number `e` of the lift at the place, and the shift w of the section on one lift has the same definition.

Lean source checked in `src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean` lines 93-95 and `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean` lines 74-74 and `src/Formalism/LocalRingCardinality/DataParams₂.lean` lines 77-78 and `src/Formalism/LocalToGlobal/Divisibility/Numbers.lean` lines 113-116.

```lean
  (∀ u0 (j : Fin m) (g : E0 × φ.A) (τ : (Fm.D x (pt u0)).what₂.Tau),
    gcode (Fm.D x (pt u0)).R.toFrame (((Fm.D x (pt u0)).eTau τ : (Fm.D x (pt u0)).R.Psi) : (Fm.D x (pt u0)).R.GG)
      = mcode φ g → w u0 j g = wj (Fm.D x (pt u0)) (j.val + 1) τ)

def wj (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  if h : j - 1 < D.R.m then (((D.hc τ).e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0

def eQ (j : ℕ) (z : RPl N.R) : ℚ :=
  if h : 1 ≤ j ∧ j ≤ N.R.m then (N.hc z).e ⟨j - 1, by omega⟩ else 0
def w (j : ℕ) (z : RPl N.R) : ℝ := ((N.eQ j z : ℚ) : ℝ)
```

`TieArith` does not mention the record `Data` or `Dd.w`, because it ties the function `w` (`φ.A → Fin m → E0 × φ.A → ℝ`) to `wj`, whereas `IdentU` (or `Ident` in `SChain.lean`) is what equates `Dd.w` with `w`. Also `wj` is indexed by `what₂.Tau` while `NumDatum.w` is indexed by `Bool × N.R.A`.

A corrected sentence replaces it with the statement below.

> `TieArith` equates the function `w u0 j g` with `wj (Fm.D x (pt u0)) (j.val + 1) τ` (which reads `(D.hc τ).e ⟨j, _⟩`), `IdentU` (or `Ident`) equates `Dd.w` of the record `Data` with `w`, and `NumDatum.w` in `Numbers.lean` reads `(N.hc z).e ⟨j - 1, _⟩` on `Bool × N.R.A`.

#### Finding 11 (The upper bound for the lattices of a datum)

The quoted sentence in `verification/strategy/README.md` lines 771-777 reads as shown below.

> The numbers `l3`, `F0` and `E1` are fields of a record, bounded by further fields of the same record.

Lean source checked in `src/Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean` lines 186-203 and `src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean` lines 91-93.

```lean
@[ext] structure IndefNum (Bs : DefBase K) where

  F0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  J0 : Bs.Tup → HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  E1 : Bs.J → ℝ

  l3 : Bs.J → ℝ

  l6 : Bs.J → ℝ

  hh : ℝ

  la : ℝ

  de : ℝ

  L3main : ∑ j, N.l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3

  errB : El3 + LG + (∑ j, (N.E1 j + E2 j)) + E3 ≤ R.errB
```

`l3`, `F0`, and `E1` are data fields of `IndefNum Bs`, which contains only eight data fields and holds no bounding inequalities at all. Instead, the sum bounds `L3main` and `errB` on `N.l3` and `N.E1` belong to the separate record `DivInputs0R` in `ConstantGeTwentyEight.lean`, while `N.F0` enters `FoOfR`.

A corrected sentence replaces it with the statement below.

> The numbers `l3`, `F0` and `E1` are data fields of `IndefNum`, while the upper bounds `L3main` and `errB` on `l3` and `E1` sit in the separate input record `DivInputs0R` and `F0` enters `FoOfR`.

#### Finding 12 (The upper bound for the lattices of a datum)

The quoted sentence in `verification/strategy/README.md` lines 773-780 reads as shown below.

> By the same reading `height_chain_atR` is submultiplicativity of the operator norm at each place, written in logarithms, with the matrices of the chain grouped by their lift.

Lean source checked in `src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean` lines 127-143.

```lean
theorem height_chain_atR {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} [Nonempty Bs.Ix] (wf : Df.WF)
    (S : IndefColsR Df Dc Sp N) (u : Dc.Mem) (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (ch : ColChain Dc u) (hP : ℝ) (hK : Bs.J → InfinitePlace K → ℝ)
    (nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hP)
    (nK : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c j.castSucc))) (ch.X j.castSucc)
      (Pi.basisFun K (Fin (ch.c j.succ))) (ch.X j.succ) v (Matrix.mulVecLin (ch.Kj j)) ^ 2 ≤
        Real.exp (∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v)) :
    (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
        (Formalism.HN.dualFrame S.XE) v (S.col.B u) ^ 2) ≤
      hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v - Real.log (S.κ v) -
        minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v))) ∧
    (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v -
        Real.log (S.κ v) - minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v))) ≤
      hP + ∑ j, (∑ v, hK j v) / (Fintype.card (InfinitePlace K) : ℝ) - ∑ j, N.l6 j - meanLog S.κ := by
```

`height_chain_atR` does not merely apply logarithmic submultiplicativity of operator norms of the chain matrices. Because `S.col.B u` composes through the quotient projection `Pq` and scaling map `ι` (`IsScalarOn` with scalar `κ v * ∏ j, lam j p v` on subspaces `Qp p`), `height_chain_atR` applies `complex_height_cast_at height_constant_bound`, subtracting `Real.log (S.κ v)` and `minOver` of the sums of `Real.log (S.lam j Bs.μ0 p v)` pointwise and subtracting `∑ j, N.l6 j` and `meanLog S.κ` after averaging over infinite places.

A corrected sentence replaces it with the statement below.

> By the same reading `height_chain_atR` invokes `complex_height_cast_at height_constant_bound` so that at each place `v` the log squared operator norm of `S.col.B u` is bounded by `hP` plus the sum of `hK l v` grouped by `ch.lf` minus `Real.log (S.κ v)` and `minOver` of the sums of `Real.log (S.lam j Bs.μ0 p v)`, and the average over infinite places is bounded by `hP` plus the averaged lift norms minus `∑ j, N.l6 j` and `meanLog S.κ`.

#### Finding 13 (The upper bound for the lattices of a datum)

The quoted sentence in `verification/strategy/README.md` lines 778-784 reads as shown below.

> `divinN_of_hypV`, which rests on 72 declarations, gets `DIVinN` from the bound of `VWin` over the host.

Lean source checked in `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean` lines 125-126 and `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean` lines 20-21.

```lean
theorem divinN_of_hypV {eps : ℝ} (Fm : FamP eps) (heps : 0 < eps) (hV : HypV Fm.toFamCore) (hN : LinkN Fm) (hR : SmallLevelRankEq Fm) :
    DIVinN Fm := by

theorem hypV_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) : HypV Fm.toFamCore :=
  ⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩
```

`divinN_of_hypV` does not take `VWin` as an argument. It proves `DIVinN Fm` from `0 < eps`, `HypV Fm.toFamCore`, `LinkN Fm`, and `SmallLevelRankEq Fm`, omitting `LinkN` and `SmallLevelRankEq` in the commentary summary while conflating `HypV` with `VWin`, which supplies the hosts via `SupplyChi` and `supplyOfAdm` before `hypV_of_cls` yields `HypV` from `(GChi ψ).cls`.

A corrected sentence replaces it with the statement below.

> `divinN_of_hypV`, which rests on 72 declarations, derives `DIVinN Fm` from `0 < eps`, `HypV Fm.toFamCore`, `LinkN Fm`, and `SmallLevelRankEq Fm`, while `VWin` enters earlier through `SupplyChi` to produce hosts and `hypV_of_cls` obtains `HypV` from `(GChi ψ).cls`.

#### Finding 14 (The chain of lifts)

The quoted sentence in `verification/strategy/README.md` lines 828-833 reads as shown below.

> That theorem rests on 14,837 declarations, and `link_brest_alt`, which carries it into the shape theorem, rests on 27,645.

Lean source checked in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkBrest.lean` lines 47-49 and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PointEvaluationSide.lean` lines 53-57.

```lean
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm), Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm → RemainingDivisionBounds Fm 2 CH :=
  fun 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie =>
    _root_.Formalism.L2.DIV.RestAll.bRest_all_alt 𝒜 2 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie

theorem definiteSideCondition_of_nprimeDef_of_nuFull (CY CT : ℝ) (hCT : 0 ≤ CT) : ∃ C0 : ℝ, ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (C CH : ℝ),
    _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide D O c b → GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) → DV.NprimeDef D O.L → D.NuFull →
      (∀ u, 0 < (D.div.Nu u).rank) → C0 ≤ c → _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH := by
  obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.T.kernel_columns_from_ties_alt CY CT hCT
```

While the declaration counts 14,837 and 27,645 match `cone.py`, `link_brest_alt` calls `bRest_all_alt` to prove `RemainingDivisionBounds Fm 2 CH` (`hh`, `bu`, `rr`, `la`) in `shape_closed_link_n_of_green` and does not depend on `rowsU_of_colPins_alt` (also confirmed by `cone.py`). Instead, `rowsU_of_colPins_alt` is used via `kernel_columns_from_ties_alt` inside `definiteSideCondition_of_nprimeDef_of_nuFull` to establish `DefiniteSideCondition`.

A corrected sentence replaces it with the statement below.

> That theorem rests on 14,837 declarations and feeds `definiteSideCondition_of_nprimeDef_of_nuFull` for `DefiniteSideCondition`, whereas `link_brest_alt`, resting on 27,645 declarations, proves `RemainingDivisionBounds` in the shape theorem without calling `rowsU_of_colPins_alt`.

#### Finding 15 (The chain of lifts)

The quoted sentence in `verification/strategy/README.md` line 852 reads as shown below.

> `BesselId` is proved by `besselId_of_joins` from join data that the field `selJ` of the record feeds.

Lean source checked in `src/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/KerJoinS.lean` lines 106-109 and `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean` lines 57-59.

```lean
theorem besselId_of_joins (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
    (hRow : ∀ F, I.eHH (D.sEE F) = conjHH X G (j F)) (hCol : ColJoinS hF I Tr)
    (hK : KerJoinS X G j Tr Y.hK Y.Dt) (hB : Formalism.BasicNotions.Rows.BuDefQ D.what₂)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D := by

def BesselId (D : D7) : Prop :=
  D.BuRational ∧ ∃ V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE, ∀ u, ∃ a : ℂ, a ≠ 0 ∧
    ∃ U : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ F, D.what₂.Bu u φ F = a * D.besS u (U φ) (V F)
```

`besselId_of_joins` proves only `Formalism.MainNotions.LocalQuadraticParts.adm13 D`, which is the second conjunct of `BesselId D` (`D.BuRational ∧ adm13 D`). The first conjunct `D.BuRational` is supplied separately through `buRat_rrFull_closed_alt` in `BrestFinalAll.lean`, and `selJ` enters `selection_closed_of_wu_decay_alt` to provide only `ComplementCountFamily`.

A corrected sentence replaces it with the statement below.

> The second conjunct `adm13 D` of `BesselId D` is proved by `besselId_of_joins` from join data fed by `selJ` via `selection_closed_of_wu_decay_alt`, while the first conjunct `D.BuRational` comes separately from `buRat_rrFull_closed_alt`.

#### Finding 16 (The bound for one lift)

The quoted sentence in `verification/strategy/README.md` reads as shown below.

> The rows are built from the k − 1 numbers v and from j of the numbers b, each shifted by the number `e` of lift j.

Lean source checked in `src/Formalism/LocalToGlobal/Divisibility/Numbers.lean` lines 131-137 and 183-191, and `src/Formalism/LocalRingCardinality/Params.lean` line 50.

```lean
def sigPar (z : RPl N.R) (i : ℕ) : ℚ :=
  if h : i < N.R.k - 1 then (N.hc z).v ⟨i, h⟩
  else if hb : i - (N.R.k - 1) < N.R.m then -(N.hc z).b ⟨i - (N.R.k - 1), hb⟩ else 0
def aPlus (j : ℕ) (z : RPl N.R) (i : ℕ) : ℚ :=
  N.sigPar z i + N.eQ j z - ((N.R.nV : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((N.R.k : ℚ) + j - 1) - ((N.R.m : ℚ) - j)) / 2
def apN (j : ℕ) (z : RPl N.R) (i : ℕ) : ℕ := ⌊N.aPlus j z i⌋.toNat
def apDiag (j : ℕ) (z : RPl N.R) : YoungDiagram :=
  YoungDiagram.ofRowLens (((List.range (N.R.sigW j).1).map (N.apN j z)).insertionSort (· ≥ ·))
    List.sortedGE_insertionSort
```

For k minus 1 up to k plus j minus 2, sigPar puts minus b (with a minus sign) rather than plus b. In addition, aPlus adds eQ j z and subtracts ((nV minus 1 minus 2 times i) divided by 2) and ((k plus j minus 1) minus (m minus j)) divided by 2 before apN takes the floor coerced to natural numbers.

A corrected sentence replaces it with the statement below.

> The `k + j − 1` candidate row inputs `apN j z i` of `apDiag` are built by taking `v₀` to `v_{k−2}` together with `-b₀` to `-b_{j−1}` in `sigPar`, adding `eQ j z`, subtracting the index-dependent and lift-dependent shifts of `aPlus`, and applying floor-to-natural-number truncation.

#### Finding 17 (The bound for one lift)

The quoted sentence in `verification/strategy/README.md` line 905 reads as shown below.

> The proof pairs each of the k − 1 lower rows of the lift with a row under the hook product, bounds the difference of each pair through the interlacing, and leaves the top row without a partner.

Lean source checked in `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean` lines 251-282 and 291-319, and `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean` lines 120-169 and 258-299.

```lean
    have hν : phRows ((Finset.univ.val.map fun i => w + c i) + blk) =
        ∑ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) + ph ((w + c (Fin.last n) : ℕ) : ℝ) +
          phRows blk := by
    have hpair : ∀ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) - ph ((r i : ℕ) : ℝ) ≤
        ((c i.castSucc : ℝ) - c' i) * Real.log A + sh * Real.log A := by
  refine ⟨fun i => νr i.castSucc.succ - wr, fun i => ar i - (wr + T), ar, νr (Fin.last (n + 1)), blk, sm,
    ⟨?_, ?_⟩, ?_, Hl, hB, ?_, rfl⟩
    have hfa2 : ∑ i : Fin (n + 1), ph ((r i : ℕ) : ℝ) =
        ph ((r 0 : ℕ) : ℝ) + ∑ i : Fin n, ph ((r i.succ : ℕ) : ℝ) := Fin.sum_univ_succ _
    have hpair : ∀ i : Fin n, ph ((w + c i : ℕ) : ℝ) - ph ((r i.succ : ℕ) : ℝ) ≤
        ((c i : ℝ) - c' i.succ) * Real.log A + sh * Real.log A := by
```

YoungDiagramTopExact.lean and YoungDiagramHook.lean do not pair every lower row 1 to k minus 1 while leaving only the top row unpaired. In young_diagram_factorial for IsRowsOff, Fin.sum_univ_castSucc splits off the last main row w plus c (Fin.last n) and hpair pairs rows 0 to n minus 1, including the top row, with r i. For IsRowsTop, top_core splits out both the top row aT plus wr and the bottom main row r0 at Fin.last (n plus 1), and young_diagram_factorial pairs only the n equals k minus 2 middle rows w plus c i with r i.succ while hrest handles aT plus w, r0, and r 0 together.

A corrected sentence replaces it with the statement below.

> In the proof via `young_diagram_factorial`, non-top places pair the upper `k − 1` rows (including the top row `0`) with the `k − 1` rows under the hook product and leave the bottom main row unpaired, while top places pair only the `k − 2` middle rows with `r i.succ` and bound both the top row `aT + w` and the bottom main row `r0` (together with `r 0`) separately.

#### Finding 18 (The bound for one lift)

The quoted sentence in `verification/strategy/README.md` line 909 reads as shown below.

> The error term of the statement grows with w, and the subsection on `ch_top` says where the main terms with w go.

Lean source checked in `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DivAssembly.lean` lines 15-46, `src/Formalism/QuotientMetricDivisors/StatementJ.lean` lines 16-31, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean` lines 118-136, `src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean` lines 31-36, `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean` lines 98-177, and `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean` lines 15-48.

```lean
  have hpt : ∀ j ρ, pq j * w j ρ * logOm + phν j ρ - fa j ρ - nν j ρ * logOm ≤
      (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) - a ρ * logOm else 0) + eE j ρ +
        |pq j - kk| * |w j ρ| * |logOm| + |δ j ρ| * |logOm| := by
def Count5 : Prop :=
  ∀ u0 (u : W u0),
    ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
        - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k) ≤ Real.log (D.T u0 u)) ∧
```

In Lean, the linear k times w times logOm terms from stepE_num and kerPlace are cancelled inside divisor_inequality_assembly against pq j times w j rho times logOm before DIV is obtained, leaving the absolute difference error |pq j minus kk| times |w j rho| times |logOm|. Meanwhile ch_top and its prerequisites Count5, key_identity5, and key_identity act on log (D.w u0 j rho times D.v divided by pi) extracted from the lower bound on log (D.T u0 u). As an interpretation, the commentary conflates the linear k times w times logOm main terms of stepE_num and kerPlace with the log w terms that ch_top receives through T u.

A corrected sentence replaces it with the statement below.

> The error term of the statement grows with `w`, while the linear `k * w * logOm` terms from `stepE_num` and `kerPlace` cancel against `pq * w * logOm` inside `divisor_inequality_assembly` before `DIV` is reached, and `Count5` and `ch_top` later carry `log w` through `log (T u)`.

#### Finding 19 (The lower bound for the lattices of a datum)

The quoted sentence in `verification/strategy/README.md` reads as shown below.

> For a family the condition `FrameRealF` asks that three times the square root of the lost share is at most σ, so the number that takes the place of η is at most 6σ.

Lean source checked in `src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean` lines 566-568 and 603-608.

```lean
def FrameRealF {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∃ de eB : ℝ, 0 ≤ de ∧ de ≤ 1 / 4 ∧ 0 ≤ eB ∧ eB ≤ 1 / 4 ∧
    (3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH ≤ 1 ∧ ∀ i : Fm.Ix x, FrameReal_at (Fm.D x i) (x ^ (-CH)) de eB
...
  refine ⟨5 * x ^ (-CH) + 3 * Real.sqrt de, eB, by positivity, f0, f4, ?_, fun i => ?_⟩
  · have h5 : 5 * x ^ (-CH) * x ^ CH = 5 := by rw [hsg, mul_assoc, inv_mul_cancel₀ hxCpos.ne', mul_one]
    calc (5 * x ^ (-CH) + 3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH
        = 5 * x ^ (-CH) * x ^ CH + (3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH := by ring
      _ ≤ 5 + 1 := by rw [h5]; linarith
      _ = 6 := by norm_num
```

`FrameRealF` asks for `(3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH ≤ 1` (which includes `4 * Real.sqrt eB`, not only `3 * Real.sqrt de`), and `frameF_of` proves `(5 * x ^ (-CH) + 3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH ≤ 6` for `FrameF`, rather than bounding `5 * x ^ (-CH) + 3 * Real.sqrt de` by `6 * x ^ (-CH)`.

A corrected sentence replaces it with the statement below.

> For a family the condition `FrameRealF` asks that 3·√`de` + 4·√`eB` is at most σ, so `frameF_of` proves that (η_B + 4·√`eB`)·x^CH is at most 6 for η_B = 5σ + 3·√`de`.

#### Finding 20 (The lower bound for the lattices of a datum)

The quoted sentence in `verification/strategy/README.md` line 1070 reads as shown below.

> The columns of all words outnumber the rows at least 19 times, since their sum is at least `Dstar`/σ with σ at most 1/20 and the rows number at most (1 + η1)·`Dstar`.

Lean source checked in `src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean` lines 31-32, 39, and 198-202.

```lean
def RsG {I : Type} [Fintype I] (ι : I → Type) [∀ i, Fintype (ι i)] : ℝ :=
  ∑ i, (Fintype.card (ι i) : ℝ)
...
  (Fintype.card α : ℝ) ≤ (1 + η1) * Dstar
...
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
```

In `JointARam`, `Dstar / sg ≤ RsG ιf` bounds the sum of the column counts `ιf` of the first factors `Bf` (giving at least `800 / 41 > 19` times `Fintype.card (κ ⊕ κ₁)` under `sg ≤ 1 / 20` and `η1 ≤ sg / 2`), whereas the word-lattice columns `ι` only satisfy `∑ i, (|ιf i| - |ι i|) ≤ de * RsG ιf` with `de ≤ 1 / 4`, which in `JointARam` yields only `(3 / 4) * (800 / 41) = 600 / 41` (about `14.63`) times `Fintype.card (κ ⊕ κ₁)`.

A corrected sentence replaces it with the statement below.

> The columns of all first factors `Bf` outnumber all rows `κ ⊕ κ₁` at least 19 times, since their sum `RsG ιf` is at least `Dstar`/σ with σ at most 1/20 and the rows `κ ⊕ κ₁` number at most (1 + η1)·`Dstar`, whereas the columns of the word lattices `Nu u` only satisfy ∑ |ι i| ≥ (1 − `de`)·`RsG ιf`, which in `JointARam` (`de` ≤ 1/4) guarantees at least 600/41 times the rows `κ ⊕ κ₁`.

## Part D, what could not be tested

Because this check inspected only the Lean text under `src/` and the working-tree strategy documents without compiling Lean or running external scripts, four categories of statements could not be tested:

- Declaration dependency counts in `README.md`. All declaration dependency counts in `README.md` (including `800,327`, `743,776`, `670,733`, `478,597`, `54,878`, `54,874`, `791`, `108`, `546`, `51,775`, `3,488`, `86`, `440`, `1,964`, `1,271`, `1,239`, `177`, `90`, `58`, `14,837`, `27,645`, `160`, `441`, `400`, `11,188`, `195,170`, `173,628`, and `463,949`) come from `verification/strategy/cone.py` and the compiled declaration graph in `verification/decl-graph/data`, not from files under `src/`, so none of those counts were recomputed here.
- Lean kernel axiom verification and compilation (`lake` and `#print axioms`). The claim under Step 10 that the five main theorems depend only on `propext`, `Classical.choice`, and `Quot.sound` was verified to match `verification/decl-graph/README.md`, and neither `lake build`, `lake comparator`, nor `#print axioms` was executed by Lean.
- Mathlib definitions and theorems outside `src/`. Mathlib objects referenced in `Statements.lean`, `ClaimStrip.lean`, and `poleData.lean` (such as `RiemannHypothesis` and analytic continuation or nonvanishing of `DirichletCharacter.LFunction`) lie outside `src/` and were checked only through their type signatures and calls inside `src/`.
- External author note and deep leaf proofs left unread in `README.md`. Citations to the external PDF note (`https://alpo.ge/remark.pdf`, such as entries 8, 13, 16, and 17) lie outside `src/` and were not checked. In addition, the internal character-count estimate for `core_ineq` (about 10,000 characters) and deep leaf proof files beyond the route interfaces (such as full proofs of `zero_density_box`, `pnt_progressions_relative_weak_holds`, `zFRDirichlet`, `derivative_integral_all`, `lipschitz_weight_all`, and upstream supply-branch internals) were not audited line by line.
