module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory

namespace GlobalTheory.HilbertSamuel.Model

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem mulW_mem_global (j : ℕ) (u : Fin G.N → F) {f : G.Sec j} (hf : f ∈ G.global j) :
    G.mulW j u f ∈ G.global (j + 1) := by
  obtain ⟨f, rfl⟩ := hf
  refine ⟨(oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul
    (H0.ofSec G.str ⊤ (G.comb u)) f, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec, G.ofSec_comb]
  simp [Geo.mulW, Fintype.linearCombination_apply]

variable {T : ℕ} (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β)





end GlobalTheory.HilbertSamuel.Model
