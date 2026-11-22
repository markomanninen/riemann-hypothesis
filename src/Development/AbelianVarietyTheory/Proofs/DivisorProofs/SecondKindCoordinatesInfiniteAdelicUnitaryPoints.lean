module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondKindCoordinatesUnitaryArchimedeanPlaStatement

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.InfChartConcat

theorem concat {G X ι : Type*} [Monoid G] (l : Filter X) (P : (ℝ → G) → Prop)
    (d : ι → ℕ) (η : ∀ j, Fin (d j) → ℝ → G) (s : ∀ j, X → Fin (d j) → ℝ)
    (hP : ∀ j i, P (η j i)) (hs : ∀ j, Tendsto (s j) l (𝓝 0)) :
    ∀ L : List ι, ∃ (m : ℕ) (η' : Fin m → ℝ → G) (s' : X → Fin m → ℝ),
      (∀ i, P (η' i)) ∧ Tendsto s' l (𝓝 0) ∧
      ∀ x, (List.ofFn fun i => η' i (s' x i)).prod =
        (L.map fun j => (List.ofFn fun i => η j i (s j x i)).prod).prod := by
  intro L
  induction L with
  | nil => exact ⟨0, Fin.elim0, fun _ => Fin.elim0, fun i => i.elim0,
      tendsto_pi_nhds.2 fun i => i.elim0, fun x => by simp⟩
  | cons j L ih =>
    obtain ⟨m, η', s', hP', hs', he⟩ := ih
    refine ⟨d j + m, Fin.append (η j) η', fun x => Fin.append (s j x) (s' x), ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hP j i
      · simpa using hP' i
    · rw [tendsto_pi_nhds]
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have := ((continuous_apply i).tendsto _).comp (hs j)
        simpa [Function.comp_def] using this
      · have := ((continuous_apply i).tendsto _).comp hs'
        simpa [Function.comp_def] using this
    · intro x
      have hf : (fun i => Fin.append (η j) η' i (Fin.append (s j x) (s' x) i)) =
          Fin.append (fun i => η j i (s j x i)) (fun i => η' i (s' x i)) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      rw [hf, List.ofFn_fin_append, List.prod_append, he x]
      simp

theorem prod_map_ite_eq {ι M : Type*} [DecidableEq ι] [Monoid M] (u : ι) (a : M) (L : List ι) :
    (L.map fun w => if w = u then a else 1).prod = a ^ L.count u := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.count_cons]
    by_cases h : w = u
    · subst h; simp [pow_succ']
    · simp [h]

theorem decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {x : GAd σ J} (hx : x ∈ infPts σ J) :
    x = ((Finset.univ : Finset (InfinitePlace F)).toList.map
      fun w => embArch σ J w (projArch σ J w x)).prod := by
  classical
  apply GAd_ext σ J
  · intro u
    rw [map_list_prod, List.map_map]
    have hf : (projArch σ J u ∘ fun w => embArch σ J w (projArch σ J w x)) =
        fun w => if w = u then projArch σ J u x else 1 := by
      funext w
      by_cases h : w = u
      · subst h; simp
      · simp [h, projArch_embArch_ne σ J (Ne.symm h)]
    rw [hf, prod_map_ite_eq, List.count_eq_one_of_mem (Finset.nodup_toList _)
      (Finset.mem_toList.2 (Finset.mem_univ _)), pow_one]
  · intro v
    rw [map_list_prod, List.map_map, (mem_infPts_iff_forall).1 hx v]
    simp [Function.comp_def]

end GlobalTheory.InfChartConcat

theorem GlobalTheory.infPts_secondKind_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ),
    (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (η i)) ∧
    Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧
    ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod := by
  intro F E _ _ _ _ _ σ hCM n J hJ
  classical
  have hp : ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J)
      (s : GArch σ J w → Fin d → ℝ), (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (η i)) ∧
      Tendsto s (𝓝 1) (𝓝 0) ∧
      ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    let A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1
    obtain ⟨d, Z, s₀, hZ, hs, hev⟩ := GlobalTheory.T.coordsSecondKind_formPreservingGroup n A
    have hd : IsUnit A.det := by
      rw [show A = J.map τ.1 from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (IsUnit.mk0 _ hJ.2).map _
    have hy : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w,
        GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z i) := by
      intro i t
      obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
      have hskew : (t • Z i)ᴴ * A + A * (t • Z i) = 0 := by
        rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
          hZ i, smul_zero]
      have hpres := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd hskew
      refine ⟨(archEquiv J hCM τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ hpres⟩, ?_⟩
      rw [GlobalTheory.Orb.archMat_eq_archEquiv J hCM, MulEquiv.apply_symm_apply]
      exact hu
    choose y hy using hy
    have hS (g : GArch σ J w) :
        GlobalTheory.Orb.archMat σ J τ g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A} := by
      rw [Set.mem_ofPred_eq, GlobalTheory.Orb.archMat_eq_archEquiv J hCM]
      exact (archEquiv J hCM τ g).2
    have hc : Tendsto (GlobalTheory.Orb.archMat σ J τ) (𝓝 1)
        (𝓝[{X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A}] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hS⟩
      simpa using (GlobalTheory.Orb.continuous_archMat σ J τ).tendsto 1
    have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ) := fun a b e =>
      (GlobalTheory.Orb.isEmbedding_archMat J hCM τ).injective (by
        show (fun i j => GlobalTheory.Orb.archMat σ J τ a i j) = fun i j =>
          GlobalTheory.Orb.archMat σ J τ b i j
        rw [e])
    refine ⟨d, fun i t => embArch σ J w (y i t), fun g => s₀ (GlobalTheory.Orb.archMat σ J τ g),
      fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨y i t, rfl, hy i t⟩⟩, hs.comp hc, ?_⟩
    filter_upwards [hc.eventually hev] with g hg
    have e : (List.ofFn fun i => embArch σ J w (y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i))).prod =
        embArch σ J w (List.ofFn fun i => y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [e]
    congr 1
    apply hinj
    rw [map_list_prod, List.map_ofFn]
    refine hg.trans (congrArg List.prod ?_)
    exact List.ofFn_inj.2 (funext fun i => (hy i _).symm)
  choose d η s hη hs he using hp
  have hproj : ∀ w, Tendsto (projArch σ J w) (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 1) := fun w => by
    have := (continuous_projArch σ J w).tendsto 1
    rw [map_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨m, η', s', hP', hs', heq⟩ := GlobalTheory.InfChartConcat.concat
    (𝓝[(infPts σ J : Set (GAd σ J))] 1) (GlobalTheory.SiegelSet.IsRealLine σ J) d η
    (fun w x => s w (projArch σ J w x)) hη (fun w => (hs w).comp (hproj w))
    (Finset.univ : Finset (InfinitePlace F)).toList
  refine ⟨m, η', s', hP', hs', ?_⟩
  have hev : ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, ∀ w, embArch σ J w (projArch σ J w x) =
      (List.ofFn fun i => η w i (s w (projArch σ J w x) i)).prod :=
    Filter.eventually_all.2 fun w => (hproj w).eventually (he w)
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hmem
  rw [heq x, List.map_congr_left (fun w _ => (hx w).symm)]
  exact GlobalTheory.InfChartConcat.decomp σ J hmem
