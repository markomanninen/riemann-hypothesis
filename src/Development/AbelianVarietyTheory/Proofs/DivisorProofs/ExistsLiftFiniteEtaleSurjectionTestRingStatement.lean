module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFiniteEtaleSurjectionTestRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.EvNatPf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_finiteEtaleSurjection_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  first | exact @GlobalTheory.exists_lift_finiteEtale_testRing | exact GlobalTheory.exists_lift_finiteEtale_testRing | (intros; apply GlobalTheory.exists_lift_finiteEtale_testRing <;> assumption)
