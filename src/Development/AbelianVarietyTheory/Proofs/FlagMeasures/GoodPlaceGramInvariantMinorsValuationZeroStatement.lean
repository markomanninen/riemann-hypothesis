module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodPlaceGramInvariantMinorsValuationZero
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlace_gramInvariant_minors_valuation_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → vE L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0 := by
  first | exact @GlobalTheory.HL.StdPlace.vE_G_D_eq_zero | exact GlobalTheory.HL.StdPlace.vE_G_D_eq_zero | (intros; apply GlobalTheory.HL.StdPlace.vE_G_D_eq_zero <;> assumption)
