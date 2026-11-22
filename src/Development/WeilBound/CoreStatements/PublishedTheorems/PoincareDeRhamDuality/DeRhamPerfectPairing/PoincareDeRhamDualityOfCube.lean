module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.MkEqZeroOfCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.Pull2ChernClassEqZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PerfectRing
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CrystallineDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem duality_of_surjAll (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange)
    (hS : SurjAll) : AbelianDeRham.Duality := by
  intro R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have iso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0 :=
    orth_of_surj hF hB hA hg (fun C _ _ A' _ φ h ↦ hS C A' g (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h)
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg))
      (LB.isLB_linComb hL _ _) (isCorrForm_lam hψ)
  exact ⟨iso, perfect_ring hF hH hB hA hg hL hψ iso⟩

end CrystallinePoints.Pd
