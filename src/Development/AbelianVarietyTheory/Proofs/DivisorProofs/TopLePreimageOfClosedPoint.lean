module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartDer

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X)
    (V : X.Opens) (h : f (closedPoint R) ∈ V) : ⊤ ≤ f ⁻¹ᵁ V := by
  intro p _
  have hp : p ⤳ closedPoint R := (PrimeSpectrum.le_iff_specializes p (closedPoint R)).1 (le_maximalIdeal p.2.ne_top)
  exact hp.mem_open (f ⁻¹ᵁ V).2 h

end GlobalTheory.ChartDer
