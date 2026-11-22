module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors

@[expose] public section

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix
open GlobalTheory.SmoothGlob (lieSet)
open scoped ContDiff

namespace GlobalTheory.GKModule

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

theorem isKStableOn_kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (kFinVec ε σ) := by
  rintro g hg v ⟨S, hS, hv, hSK⟩
  exact ⟨S, hS, hSK g hg v hv, hSK⟩

structure IsGKSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop where
  smooth : ∀ v ∈ V, SmoothVec (lieSet ε) σ v
  kFin : ∀ v ∈ V, IsKFin ε σ v
  kStable : IsKStableOn ε σ V
  lieStable : ∀ X ∈ lieSet ε, ∀ v ∈ V, dRep σ X v ∈ V

def IsAdmissibleSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop :=
  ∀ Λ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S | S ≤ V ∧ IsKTypeOf ε σ Λ S} : Submodule ℂ H)

def IsGKHom {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (ε : Fin n → Bool) (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁))
    (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) (e : kFinVec ε σ₁ →ₗ[ℂ] kFinVec ε σ₂) : Prop :=
  (∀ k ∈ Kset ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = σ₁ k v → (e w : H₂) = σ₂ k (e v)) ∧
    ∀ X ∈ lieSet ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = dRep σ₁ X v → (e w : H₂) = dRep σ₂ X (e v)

theorem isAdmissibleSub_of_finiteDimensional (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] : IsAdmissibleSub ε σ V :=
  fun _ => Submodule.finiteDimensional_of_le (sSup_le fun _ hS => hS.1)

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_det_expProd {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod).det := by
  have he : ∀ a b, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) a b := fun a b =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp
      (GlobalTheory.GardingVec.contDiff_expProd Xs)
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun s _ => contDiff_const.mul (contDiff_prod fun i _ => he _ _)

end

theorem isURepOn_det (ε : Fin n → Bool) : IsURepOn (UJset ε) (fun g => g.det • (1 : H →L[ℂ] H)) := by
  refine ⟨⟨by simp, fun a _ b _ => by ext; simp [smul_smul, mul_comm]⟩, fun g hg v => ?_, fun v => ?_⟩
  · have h1 : ‖g.det‖ = 1 := by simpa using (GlobalTheory.Published.det_isURepOn ε).1.2.1 g hg 1
    simp [norm_smul, h1]
  · have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.det • v :=
      (continuous_id.matrix_det).smul continuous_const
    simpa using this.continuousOn

theorem isGKSub_det (ε : Fin n → Bool) (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    IsGKSub ε (fun g => g.det • (1 : H →L[ℂ] H)) V ∧ IsAdmissibleSub ε (fun g => g.det • (1 : H →L[ℂ] H)) V := by
  have hK : IsKStableOn ε (fun g => g.det • (1 : H →L[ℂ] H)) V := fun g _ v hv => V.smul_mem _ hv
  refine ⟨⟨fun v _ k Xs _ => ?_, fun v hv => ⟨V, inferInstance, hv, hK⟩, hK, fun X _ v hv => ?_⟩,
    isAdmissibleSub_of_finiteDimensional _ _ _⟩
  · exact (contDiff_det_expProd Xs).smul contDiff_const
  · have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • X)).det := by
      have := (contDiff_det_expProd (fun _ : Fin 1 => X)).comp
        (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
      simpa [Function.comp_def] using this
    have h2 := ((h1.differentiable (by simp)) 0).hasDerivAt.smul_const v
    have h3 : dRep (fun g => g.det • (1 : H →L[ℂ] H)) X v = _ := h2.deriv
    rw [h3]
    exact V.smul_mem _ hv

theorem mem_UJset_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  change kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end GlobalTheory.GKModule

namespace GlobalTheory.Published

open GlobalTheory.GKModule

def AdmissibleClosure : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ V : Submodule ℂ H, IsGKSub ε σ V → IsAdmissibleSub ε σ V →
      (∀ g ∈ UJset ε, ∀ w ∈ V.topologicalClosure, σ g w ∈ V.topologicalClosure) ∧
        ∀ w ∈ V.topologicalClosure, IsKFin ε σ w → w ∈ V

def InfinitesimalEquivalence : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [Nontrivial H₁]
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [Nontrivial H₂]
    (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)),
    IsURepOn (UJset ε) σ₁ → IsIrredOn (UJset ε) σ₁ → IsURepOn (UJset ε) σ₂ → IsIrredOn (UJset ε) σ₂ →
    ∀ e : kFinVec ε σ₁ ≃ₗ[ℂ] kFinVec ε σ₂, IsGKHom ε σ₁ σ₂ e.toLinearMap →
      ∃ (U : H₁ ≃ₗᵢ[ℂ] H₂) (c : ℝ), 0 < c ∧ (∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) ∧
        ∀ v : kFinVec ε σ₁, U v = (c : ℂ) • (e v : H₂)

def GKGlobalisation : Prop := AdmissibleClosure ∧ InfinitesimalEquivalence

section Consequences

variable {n : ℕ} {ε : Fin n → Bool}

end Consequences

end GlobalTheory.Published

end
