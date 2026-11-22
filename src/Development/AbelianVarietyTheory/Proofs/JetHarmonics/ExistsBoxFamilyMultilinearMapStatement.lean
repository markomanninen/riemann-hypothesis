module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boxFamily_multilinear_map : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  intro hG R _ _ j D D' pD F _ _ k
  have hexists := GlobalTheory.BoxFamily.exists_isBoxFam hG R j D D' pD F k
  choose bx hbx using hexists
  refine ⟨⟨bx, fun s i a b => GlobalTheory.BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
    fun s i c a => GlobalTheory.BoxLinear.box_smul pD (hbx _) (hbx _)⟩,
    fun s S => ⟨fun h => GlobalTheory.BoxLinear.box_unique pD h (hbx s), ?_⟩⟩
  rintro rfl
  exact hbx s
