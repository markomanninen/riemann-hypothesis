module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingOpenLevel

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem col_mem (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (p : Fin c) :
    (fun i => d.a i p) ∈ d.lat Λ (fun _ => 1) := by
  refine ⟨0, Λ.zero_mem, Pi.single p 1, fun q => ?_, ?_⟩
  · by_cases h : q = p
    · subst h; rw [Pi.single_eq_same]; exact FractionalIdeal.one_mem_one _
    · rw [Pi.single_eq_of_ne h]; exact FractionalIdeal.zero_mem _
  · funext i; simp [mulVec_single]

theorem map_mem (d : HermitianOrthogonalExtensionData A B c ε) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {y : Fin A.rank → D.host.E}
    (hy : y ∈ Λ) : frameMat B A d.ι *ᵥ y ∈ d.lat Λ (fun _ => 1) :=
  ⟨y, hy, 0, fun _ => FractionalIdeal.zero_mem _, by simp⟩

theorem lat_eq (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) :
    d.lat Λ (fun _ => 1) = Λ.map ((frameMat B A d.ι).mulVecLin.restrictScalars (𝓞 D.host.E)) ⊔
      Submodule.span (𝓞 D.host.E) (Set.range fun p i => d.a i p) := by
  refine le_antisymm ?_ (sup_le ?_ (Submodule.span_le.2 ?_))
  · rintro _ ⟨y, hy, u, hu, rfl⟩
    refine Submodule.add_mem_sup ⟨y, hy, rfl⟩ ?_
    choose r hr using fun p => (FractionalIdeal.mem_one_iff _).1 (hu p)
    have e : d.a *ᵥ u = ∑ p, r p • fun i => d.a i p := by
      funext i
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, ← hr, Algebra.smul_def, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩; exact map_mem d hy
  · rintro _ ⟨p, rfl⟩; exact col_mem d Λ p

theorem isLattice_lat (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) : Submodule.IsFullLattice D.host.E (d.lat Λ (fun _ => 1)) := by
  have hfg : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := by
    apply Submodule.IsLattice.of_fg D.host.E
    rw [lat_eq]
    exact (hΛ.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  let S := Submodule.span D.host.E (d.lat Λ (fun _ => 1) : Set (Fin B.rank → D.host.E))
  have hmap : ∀ y : Fin A.rank → D.host.E, frameMat B A d.ι *ᵥ y ∈ S := by
    intro y
    have hy : y ∈ Submodule.span D.host.E (Λ : Set _) := by rw [hΛ.span_eq_top]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (map_mem d hy)
    | zero => simp
    | add x y _ _ hx hy => simpa only [mulVec_add] using S.add_mem hx hy
    | smul a x _ hx => simpa only [mulVec_smul] using S.smul_mem a hx
  have hcols : ∀ u : Fin c → D.host.E, d.a *ᵥ u ∈ S := by
    intro u
    have e : d.a *ᵥ u = ∑ p, u p • fun i => d.a i p := by
      funext i
      simp [mulVec, dotProduct, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => S.smul_mem _ (Submodule.subset_span (col_mem d Λ p))
  have : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := hfg
  refine ⟨?_⟩
  apply Submodule.eq_top_iff'.2
  intro x
  have h := congrArg (fun M => M *ᵥ x) (GlobalTheory.UnitaryEmbeddingGroup.decomp d hε)
  simp only [add_mulVec, ← mulVec_mulVec, one_mulVec] at h
  rw [← h]
  exact S.add_mem (hmap _) (hcols _)

end GlobalTheory.UnitaryEmbeddingOpenLevel


open GlobalTheory.UnitaryEmbeddingOpenLevel in
theorem GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → IsOpen {g : GA D V | Lev.finE V g ∈ congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪} := by
  intro D Y V d Λ 𝔪 hΛ h𝔪
  exact (congLev_open_compact V (isLattice_lat d one_ne_zero
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice Y Λ hΛ)) h𝔪).1

end
