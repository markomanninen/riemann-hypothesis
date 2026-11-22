module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfPolarisedGenericFibre
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → ∃ (σ : LB.Sec t.PP.L) (k : t.PP.L.ι), σ.f k ≠ 0 := by
  first | exact @GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt | exact GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt | (intros; apply GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt <;> assumption)
