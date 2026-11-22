module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def flagCoordMap (d : HypDec S S₀ ρ) (p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ)) : flagN d :=
  ⟨d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2),
    mul_mem (d.levi_mem_NFlag p.1.2) (mul_mem (d.nB_mem_NFlag p.2.1) (d.nC_mem_NFlag p.2.2))⟩

theorem flagCoordMap_bijective (d : HypDec S S₀ ρ) : Function.Bijective (flagCoordMap d) := by
  refine ⟨fun p q h => ?_, fun n => ?_⟩
  · rcases p with ⟨⟨u, hu⟩, b, c⟩
    rcases q with ⟨⟨v, hv⟩, b', c'⟩
    have e : d.levi u * (d.nB b * d.nC c) = d.levi v * (d.nB b' * d.nC c') :=
      congrArg Subtype.val h
    have eX := congrArg (fun g => d.pX * (mt S g * d.jX)) e
    simp only [mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX] at eX
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, Matrix.one_mul] at eX
    have huv : u = v := Units.ext eX
    subst v
    have e' := mul_left_cancel e
    have e0 := congrArg (fun g => d.pX * (mt S g * d.j0)) e'
    simp only [mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0,
      cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at e0
    subst b'
    have eY := congrArg (fun g => d.pX * (mt S g * d.jY)) (mul_left_cancel e')
    simp only [d.nC_jY, Matrix.mul_add, d.pX_jY, cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at eY
    exact Prod.ext rfl (Prod.ext rfl (Subtype.ext eY))
  · obtain ⟨T, B, hT, hX, h0⟩ := exists_blocks d n.2
    obtain ⟨u, hu, huT⟩ := Decomp.exists_unit hT
    let b := (u⁻¹).1 * B
    let g := d.levi u * d.nB b
    have hgX : mt S g * d.jX = mt S n.1 * d.jX := by
      dsimp only [g]
      rw [mt_mul, Matrix.mul_assoc, d.nB_jX, d.levi_jX, hX, huT, Matrix.mul_add, Matrix.mul_one]
    have hg0 : mt S g * d.j0 = mt S n.1 * d.j0 := by
      dsimp only [g, b]
      rw [mt_mul, Matrix.mul_assoc, d.nB_j0, h0, Matrix.mul_add,
        d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc (mt S (d.levi u)), d.levi_jX,
        Matrix.mul_assoc d.jX, ← Matrix.mul_assoc u.1, Units.mul_inv, Matrix.one_mul]
    let k := g⁻¹ * n.1
    have hkX : mt S k * d.jX = d.jX := by
      dsimp only [k]
      rw [mt_mul, Matrix.mul_assoc, ← hgX, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hk0 : mt S k * d.j0 = d.j0 := by
      dsimp only [k]
      rw [mt_mul, Matrix.mul_assoc, ← hg0, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have gram {m l : ℕ} (X : Mx D S.rank m) (Y : Mx D S.rank l) :
        adj (mt S k * X) * (gA S * (mt S k * Y)) = adj X * (gA S * Y) := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) _ Y,
        ← Matrix.mul_assoc (adj (mt S k)), GlobalTheory.MixModel.mt_unitary]
    have pY : d.pY * (mt S k * d.jY) = 1 := by
      rw [d.pY_eq, Matrix.mul_assoc, ← hkX, gram, d.gram_XY]
    have p0 : d.p0 * (mt S k * d.jY) = 0 := by
      rw [d.p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hk0, gram, d.gram_0Y, Matrix.mul_zero]
    let C := d.pX * (mt S k * d.jY)
    have hkY : mt S k * d.jY = d.jY + d.jX * C := by
      conv_lhs => rw [← Matrix.one_mul (mt S k * d.jY), ← d.sum_eq_one]
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        pY, p0, Matrix.mul_zero, add_zero, Matrix.mul_one, add_comm]
    have hC := gram d.jY d.jY
    rw [hkY, d.gram_YY] at hC
    simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY,
      d.gram_XY, cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at hC
    let c : skewA D ρ := ⟨C, eq_neg_of_add_eq_zero_left hC⟩
    have hk : k = d.nC c := d.ga_ext (hkX.trans (d.nC_jX c).symm)
      (hk0.trans (d.nC_j0 c).symm) (hkY.trans (d.nC_jY c).symm)
    refine ⟨(⟨u, hu⟩, b, c), Subtype.ext ?_⟩
    change d.levi u * (d.nB b * d.nC c) = n.1
    rw [← mul_assoc, ← hk]
    exact mul_inv_cancel_left g n.1

theorem pX_mt_flagCoord (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) =
      u.1 * (d.pX + c.1 * d.pY + b * d.p0 - (half D • (b * plus S₀ b)) * d.pY) := by
  rw [mt_mul, mt_mul, ← Matrix.mul_assoc, d.pX_levi, Matrix.mul_assoc, ← Matrix.mul_assoc d.pX, d.pX_nB]
  congr 1
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_nC, d.wittDecomp_projAnisotropic_unipotentSkew, d.pY_nC]

theorem flagCoord_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jX) = u.1 := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jX, d.pY_jX, d.p0_jX, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero]

theorem flagCoordinate_at_base (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.j0) = u.1 * b := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero, zero_add]

theorem flagCoord_jY (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jY) =
      u.1 * (c.1 - half D • (b * plus S₀ b)) := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add, Matrix.mul_sub]

theorem flagCoord_inv_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c))⁻¹ * d.jX) = (u⁻¹).1 := by
  set g := d.levi u * (d.nB b * d.nC c)
  have h1 : Formalism.L2.Theta.mt S g * d.jX = d.jX * u.1 := by
    simp only [g, mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  have h2 : Formalism.L2.Theta.mt S g⁻¹ * d.jX = d.jX * (u⁻¹).1 := by
    calc Formalism.L2.Theta.mt S g⁻¹ * d.jX = Formalism.L2.Theta.mt S g⁻¹ * (d.jX * u.1 * (u⁻¹).1) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX * (u⁻¹).1 := by
          rw [← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  rw [h2, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem flagCoord_b (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 * (d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.j0)) = b := by
  rw [flagCoordinate_at_base, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem flagCoord_c (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 * (d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jY)) + half D • (b * plus S₀ b) = c.1 := by
  rw [flagCoord_jY, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, sub_add_cancel]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

theorem flagCoord_homeo : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d,
      ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  intro D S S₀ ρ d
  have := (lattice_Mx D ρ ρ).1
  let e0 := Equiv.ofBijective _ (flagCoordMap_bijective d)
  have key : ∀ n : flagN d, (n : GA D S) =
      d.levi (e0.symm n).1.1 * (d.nB (e0.symm n).2.1 * d.nC (e0.symm n).2.2) := fun n =>
    congrArg Subtype.val (e0.apply_symm_apply n).symm
  have hM : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S) :=
    (continuous_mt S).comp continuous_subtype_val
  have hMi : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S)⁻¹ :=
    (continuous_mt S).comp continuous_subtype_val.inv
  have hU : ∀ n : flagN d, ((e0.symm n).1.1).val = d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.jX) := by
    intro n; rw [key n, flagCoord_jX]
  have hUi : ∀ n : flagN d, (((e0.symm n).1.1)⁻¹).val =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) := by
    intro n; rw [key n, flagCoord_inv_jX]
  have hB : ∀ n : flagN d, (e0.symm n).2.1 =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) * (d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.j0)) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_b d _ _ _).symm
  have hC : ∀ n : flagN d, ((e0.symm n).2.2).val =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) * (d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.jY)) +
        half D • ((e0.symm n).2.1 * plus S₀ (e0.symm n).2.1) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_c d _ _ _).symm
  have cU : Continuous fun n : flagN d => ((e0.symm n).1.1).val := by
    simp only [hU]; exact continuous_const.matrix_mul (hM.matrix_mul continuous_const)
  have cUi : Continuous fun n : flagN d => (((e0.symm n).1.1)⁻¹).val := by
    simp only [hUi]; exact continuous_const.matrix_mul (hMi.matrix_mul continuous_const)
  have cB : Continuous fun n : flagN d => (e0.symm n).2.1 := by
    simp only [hB]
    exact (continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))
  have cC : Continuous fun n : flagN d => ((e0.symm n).2.2).val := by
    have hp : Continuous fun n : flagN d => (e0.symm n).2.1 * plus S₀ (e0.symm n).2.1 :=
      cB.matrix_mul (continuous_const.matrix_mul (continuous_adj.comp cB))
    simp only [hC]
    exact ((continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))).add (hp.const_smul (half D))
  refine ⟨{ toEquiv := e0, continuous_toFun := ?_, continuous_invFun := ?_ }, fun p => rfl⟩
  · show Continuous (flagCoordMap d)
    exact Continuous.subtype_mk ((d.continuous_levi.comp (continuous_subtype_val.comp continuous_fst)).mul
      ((d.continuous_nB.comp (continuous_fst.comp continuous_snd)).mul
        (d.continuous_nC.comp (continuous_snd.comp continuous_snd)))) _
  · refine Continuous.prodMk ?_ (Continuous.prodMk cB ?_)
    · exact continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cU, cUi⟩)
    · exact continuous_induced_rng.2 cC

end GlobalTheory.MixPer
