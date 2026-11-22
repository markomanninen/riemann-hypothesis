module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset

@[expose] public section

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.LieAct

variable {n : ℕ}

theorem SmF_ext {a b : SmF n} (h : ∀ g ∈ GLs n, a.1 g = b.1 g) : a = b := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ GLs n
  · exact h g hg
  · rw [a.2.2 g hg, b.2.2 g hg]

theorem Rd_DR (X Y : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (DR Y h).1 g = Rd X (Rd Y h.1) g := by
  have hev : (DR Y h).1 =ᶠ[nhds g] Rd Y h.1 := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact DR_apply Y h hy
  change fderiv ℝ (DR Y h).1 g (g * X) = fderiv ℝ (Rd Y h.1) g (g * X)
  rw [hev.fderiv_eq]

theorem DR_add (X Y : Mat n) : DR (X + Y) = DR X + DR Y := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simpa only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, DR_apply _ _ hg] using
    congrFun (GlobalTheory.CompanionTheory.RCalc.Rd_add_left X Y h.1) g

theorem DR_smul (r : ℝ) (X : Mat n) : DR ((r : ℂ) • X) = (r : ℂ) • DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  have e : (r : ℂ) • X = r • X := by
    ext a b
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  simpa only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, DR_apply _ _ hg, e,
    Complex.real_smul, smul_eq_mul] using
    congrFun (GlobalTheory.CompanionTheory.RCalc.Rd_smul_left r X h.1) g

theorem DR_bracket (X Y : Mat n) : DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, Submodule.coe_sub, Pi.sub_apply, DR_apply _ _ hg, Rd_DR _ _ _ hg]
  exact (GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y h.2.1 hg).symm

theorem DR_lie (n : ℕ) : (∀ X Y : Mat n, DR (X + Y) = DR X + DR Y) ∧
    (∀ (r : ℝ) (X : Mat n), DR ((r : ℂ) • X) = (r : ℂ) • DR X) ∧
    (∀ X Y : Mat n, DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X) :=
  ⟨DR_add, DR_smul, DR_bracket⟩

end GlobalTheory.CompanionTheory.ModelS.LieAct
