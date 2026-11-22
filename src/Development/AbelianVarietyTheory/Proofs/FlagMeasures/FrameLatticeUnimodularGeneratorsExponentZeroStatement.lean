module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeUnimodularGeneratorsExponentZero
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
theorem _root_.GlobalTheory.T.frameLattice_unimodular_generators_exponent_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ u : Fin (2 * (r + 1)) → S.V, S.M d Λ = Submodule.span L.O (Set.range u) ∧ Submodule.span E (Set.range u) = S.ME ∧ (∀ i j, hf L S.Hm (u i) (u j) ∈ L.O) ∧ ∃ P : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (u i) (u j)) * P = 1 := by
  first | exact @GlobalTheory.HL.FrameUnimod.frame_unimodular | exact GlobalTheory.HL.FrameUnimod.frame_unimodular | (intros; apply GlobalTheory.HL.FrameUnimod.frame_unimodular <;> assumption)
