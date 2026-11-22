module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivDescendsToNumberField
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormPowSixMulDiscriminantClassInv
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariants
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurvesOfWeierstrassCurves
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

@[expose] public section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomDescentQb

theorem exists_holUnif (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : ∃ L : LB A.left, Nonempty (HolUnif A L g) := by
  have := hA.proper
  have := hA.comm
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hamp : Out.RelAmple A H :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
  exact ⟨_, GlobalTheory.RealMultChart.exists_holUnif_of_compact A g hg
    (GlobalTheory.RealMultChart.compactSpace_points A H hamp)
    (fun a n hn => GlobalTheory.RealMultChart.exists_pow_eq A hA a n hn)⟩

end GlobalTheory.HomDescentQb
