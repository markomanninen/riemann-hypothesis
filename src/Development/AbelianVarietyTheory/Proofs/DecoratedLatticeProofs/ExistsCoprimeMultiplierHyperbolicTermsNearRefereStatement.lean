module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierHyperbolicTermsNearRefere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_multiplier_hyperbolic_terms_near_reference : ∀ (D : D7) (X : HidaSetting D), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, ∀ a, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a - hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g ∧ (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
  first | exact @GlobalTheory.ScalW.ef_near_ref | exact GlobalTheory.ScalW.ef_near_ref | (intros; apply GlobalTheory.ScalW.ef_near_ref <;> assumption)
