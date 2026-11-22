module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.KeyExtLie

theorem dnRingHom_ext {R S : Type} [CommRing R] [CommRing S] {f f' : DualNumber R →+* S}
    (h1 : ∀ a, f (TrivSqZeroExt.inl a) = f' (TrivSqZeroExt.inl a)) (h2 : f DualNumber.eps = f' DualNumber.eps) : f = f' := by
  refine RingHom.ext fun x => ?_
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * DualNumber.eps := by
    ext <;> simp
  rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, h1, h1, h2]

end GlobalTheory.KeyExtLie
