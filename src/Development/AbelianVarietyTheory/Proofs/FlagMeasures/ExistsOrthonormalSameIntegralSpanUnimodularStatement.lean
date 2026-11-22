module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalSameIntegralSpanUnimodular
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
theorem _root_.GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  first | exact @GlobalTheory.HL.SelfDual.exists_orthonormal_same_span | exact GlobalTheory.HL.SelfDual.exists_orthonormal_same_span | (intros; apply GlobalTheory.HL.SelfDual.exists_orthonormal_same_span <;> assumption)
