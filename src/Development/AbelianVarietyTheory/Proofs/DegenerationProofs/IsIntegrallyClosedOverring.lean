module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsFSum
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSections
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureZmodPowEqTopOfMeetsTorsionCosets
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSection
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMemNonzeroLocusFibreOfSecBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSection
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.GoodOut

open GlobalTheory.Points

theorem exists_hom_ker {R : Type} [CommRing R] (z : PrimeSpectrum R) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (f : R →+* K), ∀ t, f t = 0 ↔ t ∈ z.asIdeal :=
  ⟨AlgebraicClosure z.asIdeal.ResidueField, inferInstance, inferInstance,
    (algebraMap z.asIdeal.ResidueField _).comp (algebraMap R z.asIdeal.ResidueField), fun _ =>
    (map_eq_zero_iff (algebraMap z.asIdeal.ResidueField _) (RingHom.injective _)).trans
      Ideal.algebraMap_residueField_eq_zero⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}


theorem exists_th_notMem (hL : Laws) (hL₂ : Laws2) (ρ : S.Real) (z : PrimeSpectrum S.R) (a : S.Gam) :
    ∃ c : S.Gam, ρ.n • c = 0 ∧ (⟨S.th (a + c), S.th_mem _⟩ : S.R) ∉ z.asIdeal := by
  obtain ⟨K, _, _, f, hf⟩ := exists_hom_ker z
  let x : Sp K ⟶ Sp S.R := spMap f
  obtain ⟨j, hj, hr⟩ := ρ.r_eq
  have hM : S.r * S.N = ρ.n * ρ.n ^ (j - 1 + ρ.k * 2) := by
    rw [hr, ρ.N_eq, ← pow_mul, ← pow_add, ← pow_succ']
    congr 1
    omega
  have hn : (ρ.n : K) ≠ 0 := by
    have h := (S.unit.map (f.comp (algebraMap o S.R))).ne_zero
    rw [map_natCast, hM, Nat.cast_mul] at h
    exact left_ne_zero_of_mul h
  obtain ⟨θ, hθ, hv⟩ := UnitTheta.exists_sec_of_baseOver S.R ρ.P ρ.th₁
  obtain ⟨y₀, hy₀, e₀⟩ := ThetaFibre.exists_mem_nonzeroLocus_fibre hL₂.secBaseChangeAny S.R ρ.P ρ.th₁ ρ.th₁_basis
    (x (IsLocalRing.closedPoint K))
  let u : Over.mk x ⟶ baseOver (Sp S.R) := Over.homMk x (by simp)
  obtain ⟨y, hy, H⟩ := UnitTheta.exists_good_point_of_sec hL.polBaseChange hL.goodPt _ ρ.P θ K x ρ.n
    ρ.n_prime.two_le hn ⟨_, hθ y₀ hy₀, _, e₀.symm⟩ (u ≫ ρ.pt a)
  have := ρ.P.isAb.comm
  obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul ρ.pt ρ.pt_add
  obtain ⟨c, hc, -⟩ := ρ.pt_bij K x y (by rw [hM, pow_mul, hy, one_pow])
  obtain ⟨a₀, -, uniq⟩ := ρ.pt_bij K x 1 (one_pow _)
  refine ⟨c, (uniq _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
    (uniq _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun h => ?_⟩
  have e : (u ≫ ρ.pt a * y).left = spMap f ≫ (ρ.pt (a + c)).left := by
    rw [← hc, ρ.pt_add]
    exact congrArg CommaMorphism.left (MonObj.comp_mul u _ _).symm
  rw [e] at H
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (H (x := IsLocalRing.closedPoint K) trivial)
  have hk' := (le_preimage_iff _ _).2 hk
  have hU := le_preimage_mono _ (Scheme.basicOpen_le _ _) hk'
  refine ((le_preimage_basicOpen_iff _ hU _).1 hk').ne_zero ?_
  rw [hv _ _ _ (ρ.th_val (a + c)) K f k hU, (hf _).2 h, zero_mul]

section Comb

variable {X Z : Scheme.{0}} (p : X ⟶ Z) {B : LB X} {J : Type} [Fintype J] (s : J → B.Sec) (W : Z.Opens)

variable [DecidableEq J] (b c : Matrix J J Γ(Z, W)) (hc : c * b = 1)
include hc

end Comb

section Transfer

variable {Z : Scheme.{0}} (P : PolAV Z)

end Transfer

variable (ρ : S.Real) (c : CubicalStr ρ.P.A ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩)


section Support

include ρ

end Support


end GlobalTheory.ZH.GoodOut

end
