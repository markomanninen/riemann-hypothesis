module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.BaseChangeMapRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.H2EqZeroOfIsInitial
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFactorsThroughMulN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.AbDual GlobalTheory.CechPic
open GlobalTheory.SerreTateDef (IsPairRed polBundle)
open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin (IsPolarisation)
open GlobalTheory.BadPt (IsWeilHom)
open GlobalTheory.PerfdLat (dualBaseChange)

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.DualTower

theorem dim_eq_of_isDual {K : Type} [Field K] (A D : AV.AbVar K) (P : LB (A.X ⊗ D.X).left)
    (h : IsDual A.X D.X P) : D.dim = A.dim := by
  obtain ⟨B, _, P₀, _, hdim, hdual, _⟩ := GlobalTheory.dualAbelianScheme _ A.X A.ab
  obtain ⟨e⟩ := GlobalTheory.Published.AbelianDualCrystal.Test.dual_unique hdual h
  have hB := hdim A.dim A.smooth
  have hne : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
  exact (GlobalTheory.relDim_unique_of_iso_grp _ hne B D.X e.hom inferInstance A.dim D.dim hB D.smooth).symm

end GlobalTheory.DualTower
