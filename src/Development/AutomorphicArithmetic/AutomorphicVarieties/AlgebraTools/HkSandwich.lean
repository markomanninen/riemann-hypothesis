module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDedekind
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOneAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeEqDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd

@[expose] public section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem simple_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H]
    (b : Bern n q H) {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := fun e => by rw [e] at h; omega
  let s := swap a c
  let d (w : Perm (Fin n)) := b.T s * b.T w - q • b.T w
  have hpair (w : Perm (Fin n)) (hw : w⁻¹ a < w⁻¹ c) : d w + d (s * w) = 0 := by
    dsimp [d, s]
    rw [b.T_mul a c h w hw, ← mul_assoc, b.T_sq a c h, add_mul, smul_mul_assoc,
      smul_mul_assoc, one_mul]
    module
  have hcancel (w : Perm (Fin n)) : d w + d (s * w) = 0 := by
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact hpair w hw
    · have hw' : (s * w)⁻¹ a < (s * w)⁻¹ c := by
        simpa [s, Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have e := hpair (s * w) hw'
      rw [show s * (s * w) = w by simp [s, swap_mul_self_mul], add_comm] at e
      exact e
  have hsum : ∑ w, d w = 0 := by
    refine Finset.sum_ninvolution (fun w => s * w) hcancel ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have he := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simpa [s, mul_assoc] using he.symm
    · intro w
      simp [s, swap_mul_self_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

private theorem symm_of_eigen {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {q : R} {H : Type} [Ring H]
    [Algebra R H] (b : Bern n q H) (hb : b.Faithful) (y : MvPolynomial (Fin n) R)
    (hy : ∀ a c : Fin n, a.val + 1 = c.val → b.T (swap a c) * (b.th y * b.one) = q • (b.th y * b.one))
    (w : Perm (Fin n)) : rename w y = y := by
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → rename (swap a c) y = y := by
    intro a c h
    have hac : a ≠ c := fun e => by rw [e] at h; omega
    obtain ⟨z, hz, e⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c h y
    have e1 := hy a c h
    rw [← mul_assoc, e, add_mul, mul_assoc, simple_one b h, mul_smul_comm, smul_mul_assoc] at e1
    have e2 : q • rename (swap a c) y + (q - 1) • (X a * z) - q • y = 0 := by
      apply hb
      rw [map_sub, map_add (f := _), map_smul, map_smul, map_smul, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
        smul_mul_assoc, e1, sub_self]
    have e3 : (C q * X c - X a) * z = 0 := by
      simp only [smul_eq_C_mul, map_sub, map_one] at e2
      linear_combination e2 - C q * hz
    rcases mul_eq_zero.1 e3 with h0 | h0
    · have := congrArg (eval fun k => if k = a then (1 : R) else 0) h0
      simp [hac.symm] at this
    · rw [h0, mul_zero] at hz
      exact (sub_eq_zero.1 hz.symm).symm
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => rename w y = y) ?_ ?_ w
  · simp
  · intro a c h w _ ih
    rw [Perm.coe_mul, ← rename_rename, ih, hs a c h]

private theorem rename_rev_NN {R : Type} [CommRing R] (n : ℕ) (q : R) :
    rename (Fin.revPerm : Perm (Fin n)) (NN n q) = ∏ p ∈ pairs n, (X p.1 - C q * X p.2) := by
  rw [NN, map_prod]
  refine Finset.prod_nbij' (fun p => (p.2.rev, p.1.rev)) (fun p => (p.2.rev, p.1.rev)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [pairs] using hp
  · intro p hp
    simpa [pairs] using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp

private theorem rename_rev_De (R : Type) [CommRing R] (n : ℕ) :
    rename (Fin.revPerm : Perm (Fin n)) (De R n) = ∏ p ∈ pairs n, (X p.1 - X p.2) := by
  simpa [NN, De] using rename_rev_NN n (1 : R)

private theorem coeff_eq {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {K : Type} [Field K]
    [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (F : Perm (Fin n) → K)
    (hF : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (∀ w : Perm (Fin n), rename w y = y) ∧
      algebraMap _ K y = ∑ u, F u * algebraMap _ K (rename u x))
    (N D : MvPolynomial (Fin n) R) (r : Perm (Fin n))
    (hr : F r = algebraMap _ K (rename r N) / algebraMap _ K (rename r D)) (v : Perm (Fin n)) :
    F v = algebraMap _ K (rename v N) / algebraMap _ K (rename v D) := by
  obtain ⟨σ, rfl⟩ : ∃ σ, v = σ * r := ⟨v * r⁻¹, by simp⟩
  let φ : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv (renameEquiv R σ).toRingEquiv
  have hφ : ∀ x : MvPolynomial (Fin n) R, φ (algebraMap _ K x) = algebraMap _ K (rename σ x) := fun x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have h0 := UpperTheory.V.AlgebraTools.hkDedekind R n K (fun u => F u - φ (F (σ⁻¹ * u))) (by
    intro x
    obtain ⟨y, hy, e⟩ := hF x
    have e' := congrArg φ e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, hy, e, map_sum] at e'
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e', sub_eq_zero]
    refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun u => ?_
    rw [map_mul, hφ, rename_rename, Equiv.coe_mulLeft, inv_mul_cancel_left, Perm.coe_mul])
  have h1 := congrFun h0 (σ * r)
  simp only [Pi.zero_apply, inv_mul_cancel_left, sub_eq_zero] at h1
  rw [h1, hr, map_div₀, hφ, hφ, rename_rename, rename_rename, Perm.coe_mul]

theorem UpperTheory.V.AlgebraTools.hkSandwich :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ x : MvPolynomial (Fin n) R, b.one * b.th x * b.one = b.th (dd (NN n q * x)) * b.one := by
  intro R _ _ n q H _ _ b hb x
  let K := FractionRing (MvPolynomial (Fin n) R)
  choose f hf hfw hf0 using UpperTheory.V.AlgebraTools.hkAct R n q H b K
  obtain ⟨-, -, -, hrev, hlt⟩ := UpperTheory.V.AlgebraTools.hkInv n
  let V := Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)
  have hdet : De R n = V.det := by
    dsimp only [V]
    rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext j
    simp
  have hD : De R n ≠ 0 := by
    rw [hdet]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr X_injective
  have hsg (w : Perm (Fin n)) : rename w (De R n) = Perm.sign w • De R n := by
    rw [hdet, AlgHom.map_det]
    have hV : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix V =
        V.submatrix w id := by
      ext i j
      simp [V, Matrix.vandermonde_apply]
    rw [hV, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
  have hsum : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      b.one * b.th x * b.one = b.th y * b.one ∧
      algebraMap _ K y = ∑ u, (∑ w, f w u) * algebraMap _ K (rename u x) := by
    intro x
    choose y hy hy' using fun w => hf w x
    refine ⟨∑ w, y w, ?_, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum, Finset.sum_mul, ← Finset.sum_congr rfl fun w _ => hy w, ← Finset.sum_mul, ← Finset.sum_mul]
        rfl
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, hy', Finset.sum_mul]
        exact Finset.sum_comm
  have hF := coeff_eq (K := K) (fun u => ∑ w, f w u) (by
    intro x
    obtain ⟨y, hy, e⟩ := hsum x
    refine ⟨y, symm_of_eigen b hb y fun a c h => ?_, e⟩
    rw [← hy, ← mul_assoc, ← mul_assoc, simple_one b h, smul_mul_assoc, smul_mul_assoc])
    (NN n q) (De R n) Fin.revPerm (by
    rw [Finset.sum_eq_single Fin.revPerm (fun w _ hw => hf0 w _ hw.symm (hlt w hw).le) (by simp), hfw, hrev,
      rename_rev_NN, rename_rev_De, map_prod, map_prod, Finset.prod_div_distrib])
  obtain ⟨y, hy, e⟩ := hsum x
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  have hD' : algebraMap _ K (De R n) ≠ 0 := fun h => hD (hinj (by rw [h, map_zero]))
  have : y = dd (NN n q * x) := by
    apply mul_left_cancel₀ hD
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [UpperTheory.V.AlgebraTools.hkDdSpec, map_mul, e, alt, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hu := hF u
    rw [hu, hsg, map_mul]
    rcases Int.units_eq_one_or (Perm.sign u) with h | h
    · rw [h, one_smul, one_smul, map_mul, ← mul_assoc, mul_div_cancel₀ _ hD']
    · rw [h, Units.neg_smul, Units.neg_smul, one_smul, one_smul, map_neg, map_neg, map_mul, div_neg, neg_mul,
        mul_neg, ← mul_assoc, mul_div_cancel₀ _ hD']
  rw [hy, this]
