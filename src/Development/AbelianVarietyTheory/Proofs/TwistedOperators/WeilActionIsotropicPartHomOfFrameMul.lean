module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoFrameAct

open scoped GlobalTheory.MixModel

theorem actO_isoPart_of_mul : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a : GL (Fin r) (AE D)) (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → ∀ (h : GA D W) (z : Mx D W.rank r), actO V W m h (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) z) (GlobalTheory.MixModel.adj a.val)) := by
  intro D V W r C a m hm h z
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram).map (incA D) =
      GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V := by
    change GlobalTheory.MixModel.rat (Cᴴ * V.gram) = _
    exact Matrix.map_mul
  have hg : GlobalTheory.MixModel.gA V * GlobalTheory.MixModel.giA V = 1 := by
    change (V.gram.map (incA D)) * (V.gram⁻¹.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have hg' : GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.gA V = 1 := by
    change (V.gram⁻¹.map (incA D)) * (V.gram.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have adjmul {l n k : ℕ} (x : Mx D l n) (y : Mx D n k) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hinv : Formalism.L2.Theta.mt V m⁻¹ = GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) := by
    have hh : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) * Formalism.L2.Theta.mt V m = 1 := by
      have hr : GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V m = GlobalTheory.MixModel.gA V := mt_rel V m
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.MixModel.adj _), hr, hg']
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V m⁻¹), ← hh, Matrix.mul_assoc]
    have hm_inv : Formalism.L2.Theta.mt V m * Formalism.L2.Theta.mt V m⁻¹ = 1 := by
      change (m.val * m⁻¹.val).val = 1
      exact congrArg Units.val (mul_inv_cancel m.val)
    rw [hm_inv, Matrix.mul_one]
  have key : GlobalTheory.MixModel.adj (C.map (incA D)) * (GlobalTheory.MixModel.gA V * (GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V))) =
      GlobalTheory.MixModel.adj a.val * (GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V) := by
    rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA V), hg, Matrix.one_mul, ← Matrix.mul_assoc, ← adjmul, hm, adjmul,
      Matrix.mul_assoc]
  change Formalism.L2.Theta.mt W h * (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) * Formalism.L2.Theta.mt V m⁻¹ = _
  rw [hinv]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart]
  rw [e]
  simp only [Matrix.mul_assoc]
  rw [key]

end GlobalTheory.IsoFrameAct

end
