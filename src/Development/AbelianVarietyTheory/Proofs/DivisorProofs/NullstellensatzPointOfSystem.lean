module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralRelation

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry CategoryTheory

open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_rat_pt {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Sp K) [LocallyOfFiniteType f]
    {Z : Set X} (hZ : IsLocallyClosed Z) {x : X} (hx : x ∈ Z) :
    ∃ a : Sp K ⟶ X, a ≫ f = 𝟙 _ ∧ ∀ w, a w ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hZ
  replace hc : IsClosed {c} := hc
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp _ _ _, fun w => by rw [pointOfClosedPoint_apply]; exact hcZ⟩

end GlobalTheory.ConeOnto
