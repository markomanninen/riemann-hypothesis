module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_weilPairAction_left_inv : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (x : WO S T), frMapO S T βS βT (actO S T g 1 x) = HMul.hMul (frMapO S T βS βT x) ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
  intro D S T βS βT g x
  have mt_one' : Formalism.L2.Theta.mt T 1 = 1 := by
    show (matHom T 1).1 = 1
    simp
  have finE_inv_val' : ((Lev.finE S g)⁻¹).1 = (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D) := by
    rw [← map_inv]; rfl
  have conj_inv_val' : ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).1 = (βS⁻¹).1 * ((Lev.finE S g)⁻¹).1 * βS.1 := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  rw [frMapO, frMapO, actO, mt_one', Matrix.one_mul, Matrix.map_mul, conj_inv_val', finE_inv_val']
  have hb : βS.1 * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1, hb, Matrix.one_mul]
