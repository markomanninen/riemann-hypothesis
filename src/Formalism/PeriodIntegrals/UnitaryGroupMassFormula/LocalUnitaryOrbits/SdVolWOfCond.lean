module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRSmulF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.LatCpt

@[expose] public section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

def CondAllF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem condV_of_all (h : CondAllF) : CondV σ J ψ v := by
  intro hs t
  rw [← h F hs.1.1 ψ hs.2.2.1 hs.2.2.2 v t]
  exact forall₂_congr fun s _ => by rw [mul_comm]

attribute [local instance] LocMassOrdSF.isModTop_tens in
private theorem fullLattice_of_isSDLoc (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hSD : IsSDLoc σ J v (L : Set (Fin n → E))) :
    Submodule.IsFullLattice E L := by
  classical
  refine { toIsLattice := hL, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro x _
  by_contra hx
  obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_le_ker_of_notMem hx
  let A := Fv F v ⊗[F] E
  let ι : E →+* A := inclR (F := F) (Fv F v)
  let f : (Fin n → A) →ₗ[A] A :=
    ∑ i : Fin n, ι (φ (Pi.single i 1)) • LinearMap.proj i
  have hf (y : Fin n → E) : f (ratV (F := F) (Fv F v) y) = ι (φ y) := by
    simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, ratV,
      smul_eq_mul]
    change (∑ i : Fin n, ι (φ (Pi.single i 1)) * ι (y i)) = _
    simp_rw [← map_mul, ← map_sum]
    congr 1
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  let fF := f.restrictScalars (Fv F v)
  let fO := fF.restrictScalars (v.adicCompletionIntegers F)
  have hfL : latLoc (E := E) v (L : Set (Fin n → E)) ≤ LinearMap.ker fO := by
    rw [latLoc, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change f (ratV (F := F) (Fv F v) y) = 0
    rw [hf, LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy)), map_zero]
  have hOpen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hSD (basLat_fg v L hL)
  obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v (hOpen.mem_nhds (Submodule.zero_mem _))
    (fun _ : Unit => ratV (F := F) (Fv F v) x)
  have hz := LinearMap.mem_ker.mp (hfL (htx ()))
  change fF (t • ratV (F := F) (Fv F v) x) = 0 at hz
  rw [map_smul] at hz
  change t • f (ratV (F := F) (Fv F v) x) = 0 at hz
  rw [hf] at hz
  exact ((map_ne_zero ι).2 hφx) ((smul_eq_zero.mp hz).resolve_left ht)

theorem sdVolW_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) : SdVolW σ J ψ v Λ a := by
  intro hS hLat hSD hU hμ
  have hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ := by
    obtain ⟨L, hL, rfl⟩ := hLat
    exact ⟨L, fullLattice_of_isSDLoc σ J v L hL hSD, rfl⟩
  have hVol := sdVolW_of_pi σ J ψ v Λ a (condV_of_all σ J ψ v hC) (dualW_of_perf σ J ψ v Λ a hP)
    (idxPiW_std σ J ψ v Λ a hS hFull) hFull
  exact hVol hS hLat hSD hU hμ

theorem sdVolH_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) :
    SdVolH σ J ψ v a := by
  intro hS
  exact sdVolH_of_pi σ J ψ v a (condV_of_all σ J ψ v hC) (dualH_of_perf σ J ψ v a hP)
    (idxPiH_std σ J ψ v a hS) hS

end PI.OmLocU.SdB
