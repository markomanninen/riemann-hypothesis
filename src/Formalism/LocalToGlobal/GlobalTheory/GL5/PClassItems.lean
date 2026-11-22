module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin
public import Formalism.PeriodIntegrals.UJClassMassAlt
public import Mathlib
public import Formalism.HermitianLattices.StatementMass
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassSteps

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_sig_ne (D : D7) : ∃ θ : D.host.E, D.sp.cm.sig θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.host.E)
  obtain ⟨θ, t, e, h⟩ := D.sp.cm.cmUnram.2.2 P hP
  refine ⟨algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ, fun h' => h ?_⟩
  have h'' : star (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ) =
      algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ := h'
  rw [h''] at e
  have : t = θ := NumberField.RingOfIntegers.coe_injective e
  rw [this, sub_self]
  exact P.zero_mem

theorem classFin_of_UJ (hF : PI.UJClassFin.UJClassFin) (D : D7) : ClassFin D := by
  intro W hW hsig
  exact hF D.host.F D.host.E D.sp.cm.sig W.rank W.gram (L0c D W) (fun _ => rfl)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1)
    (StabFin.crd_up (F := D.host.F) W) (StabFin.crd_low (F := D.host.F) W)

theorem class_number_finite (D : D7) : ClassFin D := classFin_of_UJ unitary_class_set_finite D

theorem class_number_finite_rank (D : D7) (n : ℕ) : ClassFinAt D n := classFinAt_of D (class_number_finite D) n

theorem class_mass_of_genus_classes (hM : PI.UJClassMass2.UJClassMass) (D : D7) : ClassMass D := by
  intro W hW hsig n g hcov hdisj
  classical
  have hL : Submodule.IsFullLattice D.host.E W.L0 := by
    refine { toIsLattice := W.standardTuple_isLattice, span_eq_top := ?_ }
    obtain ⟨c, hc, hlow⟩ := StabFin.crd_low (F := D.host.F) W
    let a : D.host.E := (c : D.host.F) • (1 : D.host.E)
    have ha : a ≠ 0 := by
      change (c : D.host.F) • (1 : D.host.E) ≠ 0
      rw [Algebra.smul_def, mul_one]
      exact (algebraMap D.host.F D.host.E).injective.ne (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hc)
    rw [eq_top_iff, ← W.frame.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : a • W.frame i ∈ W.L0 := by
      have h := hlow i 1 isIntegral_one
      change ∑ j, (Pi.single i a : Fin W.rank → D.host.E) j • W.frame j ∈ W.L0 at h
      rwa [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same] at h
    have hframe : W.frame i = a⁻¹ • (a • W.frame i) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hframe]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hi)
  exact hM D.host.F D.host.E D.sp.cm.sig W.V W.hT W.rank W.frame W.L0 (fun _ => rfl) (exists_sig_ne D)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) W.herm W.nondeg hL
    (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1) n g hcov hdisj



end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
