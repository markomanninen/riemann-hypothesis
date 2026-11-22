module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevel
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
theorem _root_.GlobalTheory.T.nat_coprime_of_congr_mul_one_sub_mod_level : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g → ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  first | exact @GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub | exact GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub | (intros; apply GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub <;> assumption)
