module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KerPow
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistCompare

section Basis

variable {A : Type} [CommRing A] {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

end Basis

section Hyp

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

end Hyp

section Conclusion

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R)

end Conclusion

theorem cube : Out.CubeSt :=
  GlobalTheory.AbLaw.Cube.cube_of_gen GlobalTheory.laws_without_cohomology.1 (GlobalTheory.AbLaw.exists_gen_theta
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy
    (GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1)
    GlobalTheory.AbLaw.isProjBy_tensor GlobalTheory.TrivLocus.isClosed_trivLocus
    (GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.Seesaw.seesaw
      (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.laws_without_cohomology.1
        GlobalTheory.KuennethOne.kuenneth_injective)))

theorem exists_degPre {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A) :
    ∃ (D : Out.DegPre R) (α : D.X) (e : D.P = P), e ▸ D.c α = c := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P
  choose psi hpsi using fun n : ℤ => DVR.exists_gen_of_local (V := FractionRing R) P.L P.isLB (K := PUnit)
    (fun _ => Out.ptK (c ^ n)) (fun _ => -1)
  exact ⟨{ P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := ℤ
           c := fun n => c ^ n, c_add := fun a b => zpow_add c a b, psi := psi, psi_gen := hpsi },
    (1 : ℤ), rfl, zpow_one c⟩

end GlobalTheory.TwistCompare
