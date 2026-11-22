module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviGeneratedCommutingBlockGL
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

@[expose] public section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
open Matrix in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_generated_commuting_blockGL :
    ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ) (d : Set.range b → ℕ)
      (h : ∀ c : Set.range b, (block b c).card = d c),
      ∃ f : ∀ c : Set.range b, GL (Fin (d c)) F →* levi (k := F) b,
        (∀ (c : Set.range b) (g : GL (Fin (d c)) F),
          (f c g : GL (Fin r) F) = (blockHom F b c (h c) g : GL (Fin r) F)) ∧
        (⨆ c, (f c).range) = ⊤ ∧
        ∀ c c' : Set.range b, c ≠ c' → ∀ (x : GL (Fin (d c)) F) (y : GL (Fin (d c')) F),
          Commute (f c x) (f c' y) := by
  classical
  intro F _ r b d h
  have mem_enum (c : Set.range b) (i : Fin r) :
      i ∈ Set.range (blockEnum b c (h c)) ↔ b i = c := by
    have hrange : Set.range (blockEnum b c (h c)) = (block b c : Set (Fin r)) :=
      Finset.range_orderEmbOfFin _ (h c)
    rw [hrange]
    simp [block]
  let f (c : Set.range b) : GL (Fin (d c)) F →* levi (k := F) b :=
    ((blockTri (κ := F) b).subtype.comp (blockHom F b c (h c))).codRestrict _ fun g => by
      refine mem_levi.2 fun i j hij => ?_
      show extendMat (blockEnum b c (h c)) (g : Matrix (Fin (d c)) (Fin (d c)) F) i j = 0
      rw [extendMat_out, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
      simp only [mem_enum]
      omega
  let res (c : Set.range b) : levi (k := F) b →* GL (Fin (d c)) F :=
    leviBlock b (blockEnum b c (h c)) (blockEnum b c (h c)).injective fun i j hij => by
      rw [mem_enum, ← hij, blockEnum_mem b c (h c)]
  have f_apply (c : Set.range b) (g : GL (Fin (d c)) F) :
      ((f c g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
        extendMat (blockEnum b c (h c)) (g : Matrix (Fin (d c)) (Fin (d c)) F) := rfl
  have res_apply (c : Set.range b) (m : levi (k := F) b) (a a' : Fin (d c)) :
      (res c m : Matrix (Fin (d c)) (Fin (d c)) F) a a' =
        ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (blockEnum b c (h c) a)
          (blockEnum b c (h c) a') := rfl
  have res_f (c : Set.range b) (g : GL (Fin (d c)) F) : res c (f c g) = g := by
    refine Units.ext (Matrix.ext fun a a' => ?_)
    rw [res_apply, f_apply, extendMat_in]
  have res_f_ne (c c' : Set.range b) (hc : c' ≠ c) (g : GL (Fin (d c)) F) :
      res c' (f c g) = 1 := by
    refine Units.ext (Matrix.ext fun a a' => ?_)
    rw [res_apply, f_apply, extendMat_out]
    · simp [Matrix.one_apply]
    · left
      rw [mem_enum, blockEnum_mem b c' (h c')]
      exact fun e => hc (Subtype.ext e)
  refine ⟨f, fun _ _ => rfl, ?_, ?_⟩
  · have generated : ∀ s : Finset (Set.range b), ∀ m : levi (k := F) b,
        (∀ c : Set.range b, c ∉ s → res c m = 1) → m ∈ ⨆ c : Set.range b, (f c).range := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro m hm
        have hm_one : m = 1 := by
          refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
          by_cases hij : b i = b j
          · let c : Set.range b := ⟨b i, i, rfl⟩
            obtain ⟨a, ha⟩ := (mem_enum c i).2 rfl
            obtain ⟨a', ha'⟩ := (mem_enum c j).2 hij.symm
            have hentry := res_apply c m a a'
            rw [hm c (Finset.notMem_empty _), ha, ha'] at hentry
            rw [← hentry]
            have heq : i = j ↔ a = a' := by
              rw [← (blockEnum b c (h c)).injective.eq_iff, ha, ha']
            simp [Matrix.one_apply, heq]
          · rw [m.2 i j hij]
            simp [Matrix.one_apply_ne (fun e => hij (congrArg b e))]
        rw [hm_one]
        exact Subgroup.one_mem _
      | insert c s _ ih =>
        intro m hm
        let g := f c (res c m)
        have hg : m = m * g⁻¹ * g := by simp
        rw [hg]
        refine Subgroup.mul_mem _ (ih _ fun c' hc' => ?_) (Subgroup.mem_iSup_of_mem c ⟨_, rfl⟩)
        change res c' (m * (f c (res c m))⁻¹) = 1
        by_cases hcc : c' = c
        · subst c'
          rw [map_mul, map_inv, res_f, mul_inv_cancel]
        · rw [map_mul, map_inv, res_f_ne c c' hcc, inv_one, mul_one]
          exact hm c' (by simp [hcc, hc'])
    let := Fintype.ofFinite (Set.range b)
    exact eq_top_iff.2 fun m _ => generated Finset.univ m fun c hc => absurd (Finset.mem_univ c) hc
  · intro c c' hc x y
    refine Subtype.ext (Units.ext ?_)
    change ((f c x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *
        ((f c' y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      ((f c' y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *
        ((f c x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
    rw [f_apply, f_apply]
    let e := blockEnum b c (h c)
    let e' := blockEnum b c' (h c')
    change extendMat e (x : Matrix (Fin (d c)) (Fin (d c)) F) *
        extendMat e' (y : Matrix (Fin (d c')) (Fin (d c')) F) =
      extendMat e' (y : Matrix (Fin (d c')) (Fin (d c')) F) *
        extendMat e (x : Matrix (Fin (d c)) (Fin (d c)) F)
    have disjoint (a : Fin (d c)) (a' : Fin (d c')) : e a ≠ e' a' := by
      intro he
      apply hc
      apply Subtype.ext
      rw [← blockEnum_mem b c (h c) a, ← blockEnum_mem b c' (h c') a']
      exact congrArg b he
    have hxy : (incl F e)ᵀ * incl F e' = 0 := by
      ext a a'
      simp [incl, Matrix.mul_apply, Matrix.one_apply, disjoint a a']
    have hyx : (incl F e')ᵀ * incl F e = 0 := by
      ext a' a
      simp [incl, Matrix.mul_apply, Matrix.one_apply, (disjoint a a').symm]
    let X := incl F e * ((x : Matrix (Fin (d c)) (Fin (d c)) F) - 1) * (incl F e)ᵀ
    let Y := incl F e' * ((y : Matrix (Fin (d c')) (Fin (d c')) F) - 1) * (incl F e')ᵀ
    have hXY : X * Y = 0 := by
      dsimp [X, Y]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl F e)ᵀ, hxy]
      simp
    have hYX : Y * X = 0 := by
      dsimp [X, Y]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl F e')ᵀ, hyx]
      simp
    change (1 + X) * (1 + Y) = (1 + Y) * (1 + X)
    simp only [add_mul, mul_add, hXY, hYX, one_mul, mul_one]
    abel
