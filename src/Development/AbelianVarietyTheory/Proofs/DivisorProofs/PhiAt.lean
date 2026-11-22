module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSteepOnOfGermZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

def PhiAt (y : Y₀ X Z) (ν : Valuation ((Y₀ X Z).presheaf.stalk y) (WithZero (Multiplicative ℤ))) (φ : ℝ) : Prop :=
  ∃ (T : CDVR) (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V) (ρ φT : ℝ),
    0 < ρ ∧ GlobalTheory.SlopeRec.HasPhi y' φT ∧ φ = ρ * φT ∧
    (letI := io.toAlgebra; X.ptY y'.1 =
      Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ∧
    ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)

end GlobalTheory.HSApp
