module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.PositivityModel

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H L N A : LB X}

theorem genericPoint_mem [IsIntegral X] (hd : topologicalKrullDim X = 1) {Z : Closeds X}
    (hZ : IsCompleteCurve k Z) : genericPoint X ∈ Z := by
  by_contra hn
  have h := topologicalKrullDim_add_one_le Z.isClosed isClosed_univ fun x _ =>
    ⟨genericPoint X, trivial, hn, genericPoint_specializes x⟩
  have h' := h.trans ((topologicalKrullDim_subspace_le X Set.univ).trans hd.le)
  rw [hZ.2] at h'
  exact absurd h' (by decide)

section Space
open ProjSpace
variable (k) (D : ℕ)

end Space

end GlobalTheory.PositivityModel
