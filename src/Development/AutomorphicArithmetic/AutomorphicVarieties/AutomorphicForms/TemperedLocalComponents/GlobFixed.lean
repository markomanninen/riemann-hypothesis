module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubgroupFixed

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix

namespace UpperTheory.V.Af.GlobalFixedVectors

theorem sub_fixed {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤)
    (W : Submodule ℂ V) (hW : ∀ g, ∀ v ∈ W, τ g v ∈ W) (h0 : W ≠ ⊥) (K : Subgroup Γ) (hK : HasFixed σ K) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ u ∈ K, τ u v = v :=
  _root_.UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed σ hσ τ h W hW h0 K hK

variable {F : Type} [Field F] [NumberField F] {n M : ℕ}

theorem mem_Ohat {x : Af F} : x ∈ Ohat F ↔ ∀ w : HeightOneSpectrum (𝓞 F), pLoc F w x ∈ w.adicCompletionIntegers F := by
  simp [Ohat, Subring.mem_iInf]

theorem gl_ext {g h : GL (Fin n) (Af F)}
    (e : ∀ w, GeneralLinearGroup.map (pLoc F w) g = GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin n) (w.adicCompletion F) => x i j) (e w)

theorem pLoc_sLoc (w : HeightOneSpectrum (𝓞 F)) (x : w.adicCompletion F) : pLoc F w (sLoc F w x) = x := by
  classical
  exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w x

theorem pLoc_sLoc_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : w.adicCompletion F) : pLoc F v (sLoc F w x) = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) h x

theorem sLoc_mem (w : HeightOneSpectrum (𝓞 F)) {x : Af F} (hx : x ∈ Ohat F) : sLoc F w (pLoc F w x) ∈ Ohat F :=
  mem_Ohat.2 fun v => by
    by_cases h : v = w
    · subst h; rw [pLoc_sLoc]; exact mem_Ohat.1 hx v
    · rw [pLoc_sLoc_of_ne h]; exact zero_mem _

noncomputable def eLoc (w : HeightOneSpectrum (𝓞 F)) : Ohat F →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w (pLoc F w x), sLoc_mem w x.2⟩
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem eLoc_eq (w : HeightOneSpectrum (𝓞 F)) (x : Ohat F) : eLoc w x = eLoc w 1 * x := by
  refine Subtype.ext (FiniteAdeleRing.ext _ fun v => ?_)
  change pLoc F v (sLoc F w (pLoc F w x)) = pLoc F v (sLoc F w (pLoc F w (1 : Ohat F)) * x)
  rw [map_mul]
  by_cases h : v = w
  · subst h; simp [pLoc_sLoc]
  · simp [pLoc_sLoc_of_ne h]

theorem loc_mem (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)} (hk : k ∈ KLev F n M) :
    GeneralLinearGroup.map (pLoc F w) k ∈ KLoc F w n M := by
  obtain ⟨g, hg, rfl⟩ := hk
  refine ⟨cornerGL n (eLoc w) g, ?_, ?_⟩
  · ext i j
    have h1 := congrArg (fun x : GL (Fin n) (Ohat F ⧸ Ideal.span {(M : ↥(Ohat F))}) => x i j) (MonoidHom.mem_ker.1 hg)
    change Ideal.Quotient.mk _ (g i j) = (1 : Matrix (Fin n) (Fin n) _) i j at h1
    change Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j -
      eLoc w ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j) + eLoc w (g i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [eLoc_eq w (g i j), eLoc_eq w (_ : Ohat F)]
    simp [h1, Matrix.one_apply, apply_ite (Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}))]
  · ext i j : 2
    change ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Af F) -
      sLoc F w (pLoc F w ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Ohat F)) + sLoc F w (pLoc F w (g i j)) =
      (1 : Matrix (Fin n) (Fin n) (Af F)) i j - sLoc F w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion F)) i j) +
        sLoc F w (pLoc F w (g i j))
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem tendsto_of_loc {α : Type} {𝓕 : Filter α} {f : α → Af F} {x : Af F} (hx : x ∈ Ohat F) (hf : ∀ᶠ a in 𝓕, f a ∈ Ohat F)
    (h : ∀ w, ∀ᶠ a in 𝓕, pLoc F w (f a) = pLoc F w x) : Tendsto f 𝓕 (𝓝 x) := by
  classical
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : Af F → ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun y v => if h : y ∈ Ohat F then ⟨pLoc F v y, mem_Ohat.1 h v⟩ else ⟨0, zero_mem _⟩
  have hl : ∀ y ∈ Ohat F, s (lift y) = y := fun y hy => FiniteAdeleRing.ext _ fun v => by
    change ((lift y v : _) : v.adicCompletion F) = pLoc F v y
    simp [lift, hy]
  have h1 : Tendsto (fun a => lift (f a)) 𝓕 (𝓝 (lift x)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| by
      filter_upwards [hf, h v] with a ha hav
      simp [lift, ha, hx, hav]
  have h2 := (hs.tendsto _).comp h1
  rw [hl x hx] at h2
  exact h2.congr' (hf.mono fun a ha => hl _ ha)

theorem entry_mem {k : GL (Fin n) (Af F)} (hk : k ∈ KLev F n M) (i j : Fin n) : k i j ∈ Ohat F := by
  obtain ⟨g, -, rfl⟩ := hk
  exact (g i j).2


variable (n M) in
noncomputable def KAway (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GL (Fin n) (Af F)) :=
  KLev F n M ⊓ ⨅ w ∈ S, (GeneralLinearGroup.map (pLoc F w)).ker

theorem mem_KAway {S : Finset (HeightOneSpectrum (𝓞 F))} {k : GL (Fin n) (Af F)} :
    k ∈ KAway n M S ↔ k ∈ KLev F n M ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc F w) k = 1 := by
  simp [KAway, Subgroup.mem_iInf]

theorem exists_KAway_subset {U : Set (GL (Fin n) (Af F))} (hU : U ∈ 𝓝 (1 : GL (Fin n) (Af F))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (KAway n M S : Set (GL (Fin n) (Af F))) ⊆ U := by
  classical
  by_contra hn
  push Not at hn
  choose k hk hkU using fun S => Set.not_subset.1 (hn S)
  have ent : ∀ k : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin n) (Af F), (∀ S, k S ∈ KAway n M S) →
      Tendsto (fun S => (k S).val) atTop (𝓝 1) := fun k hk =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (entry_mem (one_mem (KLev F n M)) i j) (.of_forall fun S => entry_mem (mem_KAway.1 (hk S)).1 i j) fun w => by
        filter_upwards [eventually_ge_atTop {w}] with S hS
        have e := (mem_KAway.1 (hk S)).2 w (hS (Finset.mem_singleton_self w))
        rw [← map_one (GeneralLinearGroup.map (pLoc F w))] at e
        exact congrArg (fun x : GL (Fin n) (w.adicCompletion F) => x i j) e
  have ht : Tendsto k atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent k hk).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (ent (fun S => (k S)⁻¹) fun S => inv_mem (hk S)))
  obtain ⟨S, hS⟩ := (ht.eventually hU).exists
  exact hkU S hS

end UpperTheory.V.Af.GlobalFixedVectors

