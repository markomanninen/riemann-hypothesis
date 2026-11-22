module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.DerivQuot

section Mat

variable (k : Type) [Field k]

noncomputable def eIter (n : ℕ) : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (eIter n j)

theorem glEmbMat_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) k) (a b : Fin (m + 1)) :
    glEmbMat k m A a b = if h : (a : ℕ) < m ∧ (b : ℕ) < m then A ⟨a, h.1⟩ ⟨b, h.2⟩
      else if (a : ℕ) = b then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast b =>
      have hb := b.isLt
      simp [glEmbMat, hb.ne']
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      have ha := a.isLt
      simp [glEmbMat, ha.ne]
    | cast b => simp [glEmbMat]

theorem eIter_apply (n : ℕ) : ∀ (j : ℕ) (g : GL (Fin n) k) (a b : Fin (n + j + 1)),
    (((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b =
      if h : (a : ℕ) < n ∧ (b : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨a, h.1⟩ ⟨b, h.2⟩
        else if (a : ℕ) = b then 1 else 0
  | 0, g, a, b => glEmbMat_apply k n _ a b
  | j + 1, g, a, b => by
    have e : (((eIter k n (j + 1) g : Mir k (n + (j + 1))) : GL (Fin (n + (j + 1) + 1)) k) :
        Matrix (Fin (n + (j + 1) + 1)) (Fin (n + (j + 1) + 1)) k) a b =
        glEmbMat k (n + j + 1) (((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
          Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b := rfl
    rw [e, glEmbMat_apply]
    by_cases h : (a : ℕ) < n + j + 1 ∧ (b : ℕ) < n + j + 1
    · rw [dite_eq_left h, eIter_apply n j g]
    · rw [dite_eq_right h]
      have h' : ¬ ((a : ℕ) < n ∧ (b : ℕ) < n) := fun h2 => h ⟨by omega, by omega⟩
      rw [dite_eq_right h']

theorem eIter_eq_leviEmb (n j : ℕ) (hd : ∑ a, (![n, j + 1] a) = n + j + 1) (g : GL (Fin n) k) :
    ((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g) := by
  set e := stdBlocks ![n, j + 1] hd with he
  have h0 : ∀ i : Fin n, (e ⟨0, i⟩ : ℕ) = i := fun i => by
    have := stdBlocks_val ![n, j + 1] hd 0 i
    simpa using this
  have h1 : ∀ i : Fin (j + 1), (e ⟨1, i⟩ : ℕ) = n + i := fun i => by
    have := stdBlocks_val ![n, j + 1] hd 1 i
    simpa using this
  have hsplit₀ : ∀ (a : Fin 2) (i : Fin (![n, j + 1] a)), (∃ l : Fin n, e ⟨a, i⟩ = e ⟨0, l⟩) ∨
      (∃ l : Fin (j + 1), e ⟨a, i⟩ = e ⟨1, l⟩) :=
    Fin.forall_fin_two.2 ⟨fun i => Or.inl ⟨i, rfl⟩, fun i => Or.inr ⟨i, rfl⟩⟩
  have hsplit : ∀ x : Fin (n + j + 1), (∃ i : Fin n, x = e ⟨0, i⟩) ∨ (∃ i : Fin (j + 1), x = e ⟨1, i⟩) := by
    intro x
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
    exact hsplit₀ a i
  have hv0 : ∀ (i : Fin n) (h : (e ⟨0, i⟩ : ℕ) < n), (⟨(e ⟨0, i⟩ : ℕ), h⟩ : Fin n) = i := fun i _ => Fin.ext (h0 i)
  apply Units.ext
  ext x y
  rw [eIter_apply]
  rcases hsplit x with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hsplit y with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have hi := i.isLt
    have hl := l.isLt
    rw [dite_eq_left ⟨by rw [h0]; exact hi, by rw [h0]; exact hl⟩]
    have := leviEmb_apply_same k e (firstEmb ![n, j + 1] g) 0 i l
    rw [this]
    have h2 : (firstEmb ![n, j + 1] g) 0 = g := by
      show (Pi.mulSingle (0 : Fin 2) g : ∀ a, GL (Fin (![n, j + 1] a)) k) 0 = g
      exact Pi.mulSingle_eq_same _ _
    rw [h2, hv0, hv0]
  · have hi := i.isLt
    rw [dite_eq_right (fun h => by have := h.2; rw [h1] at this; omega), ite_eq_right (by rw [h0, h1]; omega)]
    exact (leviEmb_apply_ne k e _ (a := 0) (b := 1) (by decide) i l).symm
  · have hl := l.isLt
    rw [dite_eq_right (fun h => by have := h.1; rw [h1] at this; omega), ite_eq_right (by rw [h0, h1]; omega)]
    exact (leviEmb_apply_ne k e _ (a := 1) (b := 0) (by decide) i l).symm
  · rw [dite_eq_right (fun h => by have := h.1; rw [h1] at this; omega)]
    have := leviEmb_apply_same k e (firstEmb ![n, j + 1] g) 1 i l
    rw [this]
    have h3 : (firstEmb ![n, j + 1] g) 1 = 1 := by
      show (Pi.mulSingle (0 : Fin 2) g : ∀ a, GL (Fin (![n, j + 1] a)) k) 1 = 1
      exact Pi.mulSingle_eq_of_ne (by decide) _
    rw [h3, h1, h1]
    by_cases hil : i = l
    · subst hil
      exact (ite_eq_left rfl).trans (Matrix.one_apply_eq i).symm
    · have : ¬ (n + (i : ℕ) = n + l) := fun h => hil (Fin.ext (by omega))
      rw [ite_eq_right this]
      exact (Matrix.one_apply_ne hil).symm

end Mat

section Quot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comap_twKer_phiMinus (ψ : AddChar k Circle) {m n : ℕ} (hnm : n ≤ m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (m + 1)) V) :
    (twKer (phiMinus k ψ τ) (derUnipM k m n) (derCharM k ψ m n)).comap
        (twKer τ (MirUin k (m + 1)) (mirChar k ψ m)).mkQ =
      twKer τ (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n) := by
  have twKer_eq_map {G M W : Type} [Group G] [Group M] [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ G W) (N₁ : Subgroup G) (θ₁ : N₁ →* ℂˣ) (s : M →* G)
      (hs : ∀ (m : M) (n : N₁), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N₁, θ₁ ⟨_, h⟩ = θ₁ n)
      (N₂ : Subgroup M) (θ₂ : N₂ →* ℂˣ) (N : Subgroup G) (θ : N →* ℂˣ)
      (h1 : ∀ u : N₁, ∃ h : (u : G) ∈ N, θ ⟨u, h⟩ = θ₁ u)
      (h2 : ∀ a : N₂, ∃ h : s a ∈ N, θ ⟨s a, h⟩ = θ₂ a)
      (h3 : ∀ u : N, ∃ u₁ : N₁, ∃ a : N₂, (u : G) = u₁ * s a) :
      twKer (twAct ρ N₁ θ₁ s hs) N₂ θ₂ = (twKer ρ N θ).map (twKer ρ N₁ θ₁).mkQ ∧
        twKer ρ N₁ θ₁ ≤ twKer ρ N θ := by
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    · refine Submodule.span_le.2 ?_
      rintro w ⟨a, x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        obtain ⟨h, hθ⟩ := h2 a
        refine ⟨ρ (s a) v - ((θ ⟨s a, h⟩ : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨⟨_, h⟩, v, rfl⟩, ?_⟩
        rw [hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
        rfl
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨u₁, a, hu⟩ := h3 u
      obtain ⟨hu₁, e1⟩ := h1 u₁
      obtain ⟨ha, e2⟩ := h2 a
      have hθ : θ u = θ₁ u₁ * θ₂ a := by
        have : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
        rw [this, map_mul, e1, e2]
      have hdec : ρ (u : G) v - ((θ u : ℂˣ) : ℂ) • v =
          (ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v) +
            ((θ₁ u₁ : ℂˣ) : ℂ) • (ρ (s a) v - ((θ₂ a : ℂˣ) : ℂ) • v) := by
        rw [hθ, hu, map_mul, mul_apply_eq_comp, Units.val_mul, smul_sub, mul_smul]
        abel
      have hz : ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v ∈ twKer ρ N₁ θ₁ :=
        Submodule.subset_span ⟨u₁, _, rfl⟩
      show (twKer ρ N₁ θ₁).mkQ _ ∈ twKer (twAct ρ N₁ θ₁ s hs) N₂ θ₂
      rw [hdec, map_add (f := _), Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hz, zero_add, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Submodule.Quotient.mk v, ?_⟩)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      rfl
    · refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨h, hθ⟩ := h1 u
      exact Submodule.subset_span ⟨⟨u, h⟩, v, by rw [hθ]⟩
  obtain ⟨e, hle⟩ := twKer_eq_map τ (MirUin k (m + 1)) (mirChar k ψ m) _ (levi_stab ψ m)
    (derUnipM k m n) (derCharM k ψ m n) (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n)
    (GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm) (GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm)
    (GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm)
  show (twKer (twAct τ (MirUin k (m + 1)) (mirChar k ψ m) _ (levi_stab ψ m)) (derUnipM k m n)
    (derCharM k ψ m n)).comap _ = _
  rw [e, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 hle]

theorem ker_comp_mkQ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (K : Submodule ℂ V)
    (L : Submodule ℂ (V ⧸ K)) (q : (V ⧸ K) →ₗ[ℂ] W) (h : LinearMap.ker q = L) :
    LinearMap.ker (q ∘ₗ K.mkQ) = L.comap K.mkQ := by
  rw [LinearMap.ker_comp, h]

theorem exists_quotM (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ q : τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) ∧
      ∀ (g : GL (Fin n) k) (v : τ.V), q (τ.ρ (eIter k n j g) v) = derivM k ψ j τ g (q v) := by
  intro j
  induction j with
  | zero =>
    intro τ
    exact ⟨(twKer τ.ρ (MirUin k n) 1).mkQ, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).trans (GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n _ τ.ρ), fun g v => rfl⟩
  | succ j ih =>
    intro τ
    obtain ⟨q₁, hs, hk, he⟩ := ih (MRep.phiM k ψ τ)
    refine ⟨q₁ ∘ₗ (twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ,
      hs.comp (Submodule.mkQ_surjective _), ?_, fun g v => he g (Submodule.Quotient.mk v)⟩
    exact (ker_comp_mkQ _ _ q₁ hk).trans (comap_twKer_phiMinus ψ (Nat.le_add_right n j) τ.ρ)

theorem exists_deriv_quot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    ∃ q : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) ∧
      ∀ (g : GL (Fin n) k) (v : V), q (π (leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g)) v) =
        GlobalTheory.BZMir.deriv k ψ j π g (q v) := by
  intro k _ _ _ _ ψ n j V _ _ π hd
  obtain ⟨q, hs, hk, he⟩ := exists_quotM ψ n j (resM k π)
  refine ⟨q, hs, hk.trans (GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM k ψ (n + j) n V π), fun g v => ?_⟩
  rw [← eIter_eq_leviEmb k n j hd g]
  exact he g v

end Quot

end GlobalTheory.CompanionTheory.DerivQuot

end
