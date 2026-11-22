module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearArt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxLimPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxExtA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] {x y : R}
    (h : ∀ N : ℕ, x - y ∈ maximalIdeal R ^ (N + 1)) : x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ N => exact h N

private theorem nontrivial_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ) :
    Nontrivial (R ⧸ maximalIdeal R ^ (N + 1)) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  apply (maximalIdeal.isMaximal R).ne_top
  exact top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N))

private theorem isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ)
    [IsLocalRing (R ⧸ maximalIdeal R ^ (N + 1))] :
    IsNilpotent (maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1))) := by
  refine ⟨N + 1, ?_⟩
  have hle : maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1)) ≤
      (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1))) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map _)
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  calc _ ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1)))) ^ (N + 1) :=
        Ideal.pow_right_mono hle _
    _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem UpperTheory.V.Ws.sxNearA :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hQ
  classical
  have liftNilpotent : ∀ (T : Type) [CommRing T] [Algebra Λ T] [IsCO Λ T] (P : RD Φ T),
      IsNilpotent (maximalIdeal T) → Φ.Near a τ P → ∃ f : W.A →ₐ[Λ] T, D'.map (f : W.A →+* T) = P := by
    intro T _ _ _ P hnil hP
    let c := ∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs
    have hc : ∀ i j, -(c : ℤ) ≤ τ (wt i j) := by
      intro i j
      have h : (τ (wt i j)).natAbs ≤ c :=
        Finset.single_le_sum (f := fun p : Fin 4 × Fin 4 => (τ (wt p.1 p.2)).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
      omega
    obtain ⟨S, _, _, _, e, he⟩ := sxLaur (Λ := Λ) hnil c
    obtain ⟨P', hP', hr, hψ⟩ := sxScaleRD hnil he hc hP
    obtain ⟨F, hF, -⟩ := hU.2 S P' hP'
    have hFr : ∀ g i j, e (F (D.r g i j)) = HahnSeries.single (τ (wt i j)) (P.r g i j) := by
      intro g i j
      rw [← hr, ← hF]
      rfl
    have hFψ : ∀ v i s, e (F (D.ψ v i s)) = HahnSeries.single 0 (P.ψ v i s) := by
      intro v i s
      rw [← hψ, ← hF]
      rfl
    have hz : ∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y := by
      intro s
      rcases hG.var s with ⟨g, i, j, x, h1, h2, h3⟩ | ⟨v, i, t, x, h1, h2⟩
      · rw [h1, h2, map_sub, map_sub, hFr, AlgHom.commutes, he.alg]
        by_cases hij : i = j
        · rw [(wt_eq_zero i j).2 hij, map_zero]
          exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
        · rw [h3 hij]
          exact ⟨P.r g i j, by simp⟩
      · rw [h1, h2, map_sub, map_sub, hFψ, AlgHom.commutes, he.alg, map_zero]
        exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
    obtain ⟨f, hf⟩ := sxLaurDesc W he τ F (sxLaurPart W hG.max he τ F hz)
    have er : ∀ g i j, ((D'.r g i j : W.A) : R) = D.r g i j := by
      intro g i j
      rw [← hD']
      rfl
    have eψ : ∀ v i s, ((D'.ψ v i s : W.A) : R) = D.ψ v i s := by
      intro v i s
      rw [← hD']
      rfl
    refine ⟨f, RD.ext ?_ ?_⟩
    · ext g i j
      have hm : D'.r g i j ∈ W.gr (wt i j) := by
        show ((D'.r g i j : W.A) : R) ∈ W.part (wt i j)
        rw [er]
        exact hG.ent g i j
      have h := hf _ _ hm
      rw [er, hFr] at h
      exact (HahnSeries.single_injective _ h).symm
    · funext v i
      ext s
      have hm : D'.ψ v i s ∈ W.gr 0 := by
        show ((D'.ψ v i s : W.A) : R) ∈ W.part 0
        rw [eψ]
        exact hG.chr v i s
      have h := hf _ _ hm
      rw [eψ, hFψ, map_zero] at h
      exact (HahnSeries.single_injective _ h).symm
  have hlev : ∀ N : ℕ, ∃ f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) := by
    intro N
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact liftNilpotent _ _ (isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ N)
      (sxNearMap (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))) hQ)
  have hval : ∀ s : W.σ, ∃ y : R', ∀ (N : ℕ) (f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) →
      f (W.zA s) = Ideal.Quotient.mk _ y := by
    intro s
    rcases hG.var s with ⟨g, i, j, c, hz, -, -⟩ | ⟨v, i, t, c, hz, -⟩
    · refine ⟨Q.r g i j - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.r g i j = ((D'.r g i j : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.r g i j) = Ideal.Quotient.mk _ (Q.r g i j) :=
        congrArg (fun E => E.r g i j) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
    · refine ⟨Q.ψ v i t - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.ψ v i t = ((D'.ψ v i t : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.ψ v i t) = Ideal.Quotient.mk _ (Q.ψ v i t) :=
        congrArg (fun E => E.ψ v i t) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
  choose y hy using hval
  choose fN hfN using hlev
  have huniq : ∀ (N : ℕ) (f f' : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
    intro N f f' h
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact sxExtA W hG.max _ f f' h
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := Λ)
  obtain ⟨F, hF⟩ := sxLimPt (Λ := Λ) (maximalIdeal R') W.zA y
    (fun N => ⟨fN N, fun s => hy s N (fN N) (hfN N)⟩) huniq
  have hcomp : ∀ N, (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))).comp F = fN N := by
    intro N
    apply huniq
    intro s
    rw [AlgHom.comp_apply, hF s, hy s N (fN N) (hfN N)]
    rfl
  have hpt : ∀ (x : W.A) (q : R'), (∀ N, fN N x = Ideal.Quotient.mk _ q) → F x = q := by
    intro x q hx
    apply eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete
    intro N
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hx N, ← hcomp N]
    rfl
  refine ⟨F, ?_⟩
  apply RD.ext
  · ext g i j
    exact hpt _ _ (fun N => congrArg (fun E => E.r g i j) (hfN N))
  · funext v i
    ext t
    exact hpt _ _ (fun N => congrArg (fun E => E.ψ v i t) (hfN N))
