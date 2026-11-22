module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniqueness
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MoveQkCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftFiniteCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibreStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIso

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLoc.TraitOrd

section Specialise

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} [IsOpenImmersion j]
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

theorem isSemiAbelian_of_isGrpPullback {T : Scheme.{0}} {f : T ⟶ S} {G' : Over T} [GrpObj G'] [IsCommMonObj G']
    {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

end Specialise

theorem eq_of_associated_pow {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)


end GlobalTheory.SiegLoc.TraitOrd
