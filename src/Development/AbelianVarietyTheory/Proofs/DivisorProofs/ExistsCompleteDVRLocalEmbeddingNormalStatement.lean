module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRLocalEmbeddingNormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_local_embedding_normal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j := by
  first | exact @GlobalTheory.CompleteNormalDvr.exists_dvr_isCN | exact GlobalTheory.CompleteNormalDvr.exists_dvr_isCN | (intros; apply GlobalTheory.CompleteNormalDvr.exists_dvr_isCN <;> assumption)
