module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ), (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite → ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  first | exact @GlobalTheory.orbit_finite_mem_finite_ext | exact GlobalTheory.orbit_finite_mem_finite_ext | (intros; apply GlobalTheory.orbit_finite_mem_finite_ext; all_goals assumption)
