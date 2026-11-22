module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.LineNorm.Glue

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

variable {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y}

theorem below_mem (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W) :
    N.j (below y.1) ∈ W := by
  change (y.1 ≫ N.j) _ ∈ W
  rw [← h]
  exact hW (x := spMap e.O.subtype _) trivial

theorem w_le_one (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W)
    (g : Γ(N.X, W)) (hg : genericPoint Y.X ∈ N.j ⁻¹ᵁ W) :
    e.w (valAt y.1 (fnOf (N.j ⁻¹ᵁ W) hg (N.j.app W g))) ≤ 1 := by
  have hb : below y.1 ∈ N.j ⁻¹ᵁ W := below_mem N h hW
  have ht : ⊤ ≤ y.1 ⁻¹ᵁ (N.j ⁻¹ᵁ W) := fun p _ => by
    change (y.1 ≫ N.j) p ∈ W
    rw [← h]
    exact hW (x := spMap e.O.subtype p) trivial
  have hev := OfModel.eval_pull e.O.subtype N.j y.1 yt h (U := W) (W := N.j ⁻¹ᵁ W) le_rfl ht hW g
  rw [OfModel.valAt_fnOf _ hb ht, Scheme.Hom.app_eq_appLE, hev, ← e.mem_O]
  exact Subtype.prop _

end GlobalTheory.LineNorm.Glue
