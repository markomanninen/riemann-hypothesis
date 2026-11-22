module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

namespace I195MixedCoordinates_b311a3746f35afef36fdd39b

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_b311a3746f35afef36fdd39b

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ThetaMixInj

variable {D : D7}

theorem psi_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) : ψ t ≠ 0 := by
  intro h
  have e := ψ.map_add_eq_mul t (-t)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e

theorem heisO_two (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u v : WO S T) (f : WO S T → ℂ) (z : WO S T) :
    heisO ψ S T u (heisO ψ S T v f) z = ψ (symplOH S T z u) * (ψ (symplOH S T (z + u) v) * f (z + u + v)) := rfl

theorem heisO_three (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u v t : WO S T) (f : WO S T → ℂ) (z : WO S T) :
    heisO ψ S T u (heisO ψ S T v (heisO ψ S T t f)) z =
      ψ (symplOH S T z u) * (ψ (symplOH S T (z + u) v) * (ψ (symplOH S T (z + u + v) t) * f (z + u + v + t))) := rfl

theorem incAdj_surj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (η : Mx D ρ S.rank) :
    ∃ y, d.incAdj S y = d.incY S η := by
  refine ⟨adj (incA D (-D.host.xi0) • (η ⬝ giA S)), ?_⟩
  rw [HypDec.incAdj_apply, adj_adj, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, smul_smul,
    ← map_mul, neg_mul_neg, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul]

theorem wittHyperbolic_symplecticPairing_core_dual_eq_zero {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (w : WO S T₀) (η : Mx D ρ S.rank) :
    symplOH S T (d.inc0 S w) (d.incY S η) = 0 := by
  have h := d.hO_inc S 0 0 0 η w 0
  simp only [map_zero, zero_add, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]


set_option maxHeartbeats 1000000 in
theorem mixT_incAdj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (g : WO S T → ℂ) (y y' : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ μ 𝓕 (heisO ψ S T (d.incAdj S y') g) y = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ μ 𝓕 g (y + y') := by
  set_option backward.isDefEq.respectTransparency false in
    funext w₀
    unfold _root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target
    refine congrArg (fun F : Mx D ρ S.rank → ℂ => ∫ ξ in 𝓕, F ξ ∂μ) (funext fun ξ => ?_)
    change heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) (heisO ψ S T (d.incAdj S y') g))) 0 = heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S (y + y')) (heisO ψ S T (d.inc0 S w₀) g)) 0
    rw [HypDec.integrandT_eq, HypDec.integrandT_eq, heisO]
    have e1 : symplOH S T (d.incX S ξ + d.incAdj S y + d.inc0 S w₀) (d.incAdj S y') =
        symplOH S T (d.incX S ξ) (d.incAdj S y') := by
      rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_left]
      simp only [HypDec.incAdj_apply, HypDec.symplOH_incY_incY, wittHyperbolic_symplecticPairing_core_dual_eq_zero, add_zero]
    have e2 : d.incX S ξ + d.incAdj S y + d.inc0 S w₀ + d.incAdj S y' = d.incX S ξ + d.incAdj S (y + y') + d.inc0 S w₀ := by
      rw [map_add (f := _)]; abel
    rw [e1, e2, ← mul_assoc, ← AddChar.map_add_eq_mul, ← GlobalTheory.OrientedHeis.symplOH_add_right, ← map_add (f := _)]

theorem source {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') {S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (v : VolM D T.rank ρ) (h : ∀ x, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 f x = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 f' x) : f = f' := by
  set_option backward.isDefEq.respectTransparency false in
    have L := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v
    funext z
    have hz : z = d.extX T (z ⬝ d.jX) + d.ext0 T (z ⬝ d.j0) + d.extY T (z ⬝ d.jY) :=
      ((d.coordS T).symm_apply_apply z).symm
    generalize z ⬝ d.jX = a at hz
    generalize z ⬝ d.j0 = w at hz
    generalize z ⬝ d.jY = b at hz
    subst hz
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.extY T b)
    have hg' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf' (d.extY T b)
    have hk := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (d.extX T a)
    have hk' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg' (d.extX T a)
    have hmix : ∀ x, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) (heisO ψ S T (d.extY T b) f)) x =
        (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) (heisO ψ S T (d.extY T b) f')) x := fun x => by
      change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 _ x = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 _ x
      change ∀ x, I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 f x = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 f' x at h
      rw [(L _ hg).1 x a, (L _ hg').1 x a, (L f hf).2.1 (x + a) b, (L f' hf').2.1 (x + a) b, h]
    have e1 := (L _ hk).2.2.2.2 w
    have e2 := (L _ hk').2.2.2.2 w
    change ∀ x, I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 _ x = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 _ x at hmix
    have hv := e1.unique (by convert e2 using 1; exact funext fun x => congrFun (hmix (rat x)) _)
    rw [heisO_two, heisO_two] at hv
    have p : d.ext0 T w + d.extX T a + d.extY T b = d.extX T a + d.ext0 T w + d.extY T b := by abel
    rw [p] at hv
    exact mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) hv)

theorem target {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') {T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)
    (v : VolM D ρ S.rank) (h : ∀ y, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕 f y = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕 f' y) : f = f' := by
  set_option backward.isDefEq.respectTransparency false in
    have L := GlobalTheory.HeisTarget.main D ψ hψ S T T₀ ρ d v.μ v.𝓕 v.covol
    funext z
    obtain ⟨y, hy⟩ := incAdj_surj d S (d.pY ⬝ z)
    have hz : z = d.incX S (d.pX ⬝ z) + d.inc0 S (d.p0 ⬝ z) + d.incAdj S y := by
      rw [hy]; exact ((d.coordT S).symm_apply_apply z).symm
    generalize d.pX ⬝ z = ξ at hz
    generalize d.p0 ⬝ z = w at hz
    subst hz
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.incAdj S y)
    have hg' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf' (d.incAdj S y)
    have hk := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (d.inc0 S w)
    have hk' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg' (d.inc0 S w)
    have hm := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hk (d.incX S ξ)
    have hm' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hk' (d.incX S ξ)
    have hmix : ∀ y₀, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕
          (heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.inc0 S w) (heisO ψ S T (d.incAdj S y) f))) y₀ =
        (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕
          (heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.inc0 S w) (heisO ψ S T (d.incAdj S y) f'))) y₀ := fun y₀ => by
      change I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 _ y₀ = I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 _ y₀
      rw [(L _ hk).1 ξ y₀, (L _ hk').1 ξ y₀, (L _ hg).2.1 w y₀, (L _ hg').2.1 w y₀]
      have hh : I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 (heisO ψ S T (d.incAdj S y) f) y₀ = I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 (heisO ψ S T (d.incAdj S y) f') y₀ := by
        change _root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d S ψ v.μ v.𝓕 _ _ = _root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d S ψ v.μ v.𝓕 _ _
        rw [mixT_incAdj, mixT_incAdj, h]
      rw [hh]
    have e1 := (L _ hm).2.2
    have e2 := (L _ hm').2.2
    change ∀ y₀, I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 _ y₀ = I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 _ y₀ at hmix
    have hv := e1.unique (by convert e2 using 1; exact funext fun x => congrFun (hmix (rat x)) _)
    rw [heisO_three, heisO_three, zero_add] at hv
    exact mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) hv))

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f f' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ), (∀ x, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 f x = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 f' x) → f = f') ∧ ∀ (T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank), (∀ y, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕 f y = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕 f' y) → f = f' :=
  fun _ _ hψ _ _ _ _ hf hf' =>
    ⟨fun _ _ d v h => source hψ hf hf' d v h, fun _ _ d v h => target hψ hf hf' d v h⟩

end GlobalTheory.ThetaMixInj
