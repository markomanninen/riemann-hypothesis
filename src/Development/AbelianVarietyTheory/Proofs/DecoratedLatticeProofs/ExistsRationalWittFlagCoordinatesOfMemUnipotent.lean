module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructureStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatCoord


set_option maxHeartbeats 1000000 in
theorem coords_rat {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank)
    (u : GL (Fin ρ) (AE D)) (hQ : d.nC c' * (d.nB b' * d.levi u) ∈ GQ V) :
    c'.1 ∈ ratMx D ρ ρ ∧ b' ∈ ratMx D ρ V₀.rank ∧ u.1 ∈ ratMx D ρ ρ ∧ (u⁻¹).1 ∈ ratMx D ρ ρ := by
  generalize hg : d.nC c' * (d.nB b' * d.levi u) = g at hQ
  have hM : mt V g ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g).1 hQ
  have hM' : mt V g⁻¹ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g⁻¹).1 (inv_mem hQ)
  have hX : mt V g ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (d.nB_jX _), cancel₂ (d.nC_jX _)]
  have hX' : mt V g⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1 := by
    calc mt V g⁻¹ ⬝ d.jX = mt V g⁻¹ ⬝ (d.jX ⬝ u.1 ⬝ (u⁻¹).1) := by
          rw [Matrix.mul_assoc d.jX, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have h0 : mt V g ⬝ d.j0 = d.j0 + d.jX ⬝ b' := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.nB_j0, Matrix.mul_add, cancel₂ (d.nC_jX _), d.nC_j0]
  have hY : d.pX ⬝ (mt V g ⬝ d.jY) = (c'.1 - half D • (b' ⬝ plus V₀ b')) ⬝ adj (u⁻¹).1 := by
    rw [← hg, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, cancel₂ (d.nB_jY _)]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₂ (d.nC_jY _),
      cancel₂ (d.nC_j0 _), cancel₂ (d.nC_jX _), cancel₂ d.pX_jY, cancel₂ d.pX_jX, cancel₂ d.pX_j0,
      Matrix.one_mul, Matrix.zero_mul, zero_add, sub_zero]
  have hu1 : u.1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g ⬝ d.jX) = u.1 := by rw [hX, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hu2 : (u⁻¹).1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g⁻¹ ⬝ d.jX) = (u⁻¹).1 := by rw [hX', cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM' (rat_mem _))
  have hb : b' ∈ ratMx D ρ V₀.rank := by
    have e : d.pX ⬝ (mt V g ⬝ d.j0) = b' := by
      rw [h0, Matrix.mul_add, d.pX_j0, zero_add, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hc : c'.1 = d.pX ⬝ (mt V g ⬝ d.jY) ⬝ adj u.1 + half D • (b' ⬝ plus V₀ b') := by
    have e : adj (u⁻¹).1 ⬝ adj u.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
    rw [hY, Matrix.mul_assoc, e, Matrix.mul_one, sub_add_cancel]
  refine ⟨?_, hb, hu1, hu2⟩
  rw [hc]
  exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))) (ratMx_adj hu1))
    (ratMx_smul _ (ratMx_mul hb (ratMx_mul (rat_mem _) (ratMx_adj hb))))

theorem rat_coords_of_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ (c : skewA D ρ) (b : Mx D ρ V₀.rank) (u : UX D ρ), γ = d.nC c * (d.nB b * d.levi u.1) ∧ c.1 ∈ ratMx D ρ ρ ∧ b ∈ ratMx D ρ V₀.rank ∧ u ∈ UXQ D ρ := by
  intro D V V₀ ρ d γ hQ hN
  obtain ⟨T, b, hT, hX, h0⟩ := exists_blocks d hN
  obtain ⟨u, hu, hu1⟩ := GlobalTheory.MixPer.Decomp.exists_unit hT
  let g := d.nB b * d.levi u
  let n := g⁻¹ * γ
  have fixed {k : ℕ} {X : Mx D V.rank k} (h : mt V γ ⬝ X = mt V g ⬝ X) : mt V n ⬝ X = X := by
    rw [show n = g⁻¹ * γ from rfl, mt_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, mt_inv_mul,
      Matrix.one_mul]
  have fixX : mt V n ⬝ d.jX = d.jX := fixed (by
    rw [hX, show g = d.nB b * d.levi u from rfl, mt_mul, Matrix.mul_assoc, d.levi_jX,
      cancel₂ (d.nB_jX b), hu1, Matrix.mul_add, Matrix.mul_one])
  have fix0 : mt V n ⬝ d.j0 = d.j0 := fixed (by
    rw [h0, show g = d.nB b * d.levi u from rfl, mt_mul, Matrix.mul_assoc,
      d.wittDecomp_levi_inclAnisotropic, d.nB_j0])
  have gram {k l : ℕ} (X : Mx D V.rank k) (Y : Mx D V.rank l) :
      adj (mt V n ⬝ X) ⬝ (gA V ⬝ (mt V n ⬝ Y)) = adj X ⬝ (gA V ⬝ Y) := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V) _ Y, ← Matrix.mul_assoc (adj (mt V n)),
      GlobalTheory.MixModel.mt_unitary]
  let c := d.pX ⬝ (mt V n ⬝ d.jY)
  have imageY : mt V n ⬝ d.jY = d.jY + d.jX ⬝ c := by
    have projY : d.pY ⬝ (mt V n ⬝ d.jY) = 1 := by
      rw [d.pY_eq, Matrix.mul_assoc, ← fixX, gram, d.gram_XY]
    have proj0 : d.p0 ⬝ (mt V n ⬝ d.jY) = 0 := by
      rw [d.p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← fix0, gram, d.gram_0Y, Matrix.mul_zero]
    conv_lhs => rw [← Matrix.one_mul (mt V n ⬝ d.jY), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, proj0, projY, Matrix.mul_zero, Matrix.mul_one, add_zero]
    exact add_comm _ _
  have skew : c ∈ skewA D ρ := by
    have h := gram d.jY d.jY
    rw [imageY, d.gram_YY] at h
    simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY, d.gram_XY,
      cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
      Matrix.mul_one, add_zero, zero_add] at h
    exact eq_neg_of_add_eq_zero_left h
  let c₀ : skewA D ρ := ⟨c, skew⟩
  have hn : n = d.nC c₀ := d.ga_ext (fixX.trans (d.nC_jX c₀).symm) (fix0.trans (d.nC_j0 c₀).symm)
    (imageY.trans (d.nC_jY c₀).symm)
  have hγ : γ = d.nC (skewConj u.1 c₀) * (d.nB b * d.levi u) := by
    calc
      γ = g * n := (mul_inv_cancel_left g γ).symm
      _ = _ := by rw [hn, show g = d.nB b * d.levi u from rfl, mul_assoc, d.levi_mul_nC,
        ← mul_assoc, ← d.nC_mul_nB, mul_assoc]
  rw [hγ] at hQ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := coords_rat d _ _ u hQ
  exact ⟨skewConj u.1 c₀, b, ⟨u, hu⟩, rfl, h1, h2, h3, h4⟩

end GlobalTheory.RatCoord

end
