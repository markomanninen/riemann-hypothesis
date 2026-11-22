module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorObject_extends_over_dvr_of_abelianModel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (o : Obj b N (spMap ((algebraMap W L).comp gm))) (G : Over (Sp W)) [GrpObj G] (φ : o.A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback o.A G (spMap (algebraMap W L)) φ → ∃ o' : Obj b N (spMap gm), Nonempty (ObjMap o o' (spMap (algebraMap W L))) := by
  first | exact @GlobalTheory.HTObjExt.extends_obj | exact GlobalTheory.HTObjExt.extends_obj | (intros; apply GlobalTheory.HTObjExt.extends_obj <;> assumption)
