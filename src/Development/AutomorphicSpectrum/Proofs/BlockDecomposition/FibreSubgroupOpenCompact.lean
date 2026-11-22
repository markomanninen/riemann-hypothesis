module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UMLeviMulUMLevi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem colv_uM_mul_levi (n : ℕ) (y : Fin n → k) (b : GL (Fin n) k) :
    GlobalTheory.CompanionTheory.MirLevi.colv (uM k n y * levi k n b) = y := by
  have hu : ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k n y := by
    first
    | rfl
    | (ext a c; simp [GlobalTheory.CompanionTheory.BZPsiPG.uM, GlobalTheory.BZMir.unip])
  have hL : ((GlobalTheory.BZMir.levi k n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k n (b : Matrix (Fin n) (Fin n) k) := rfl
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv, Subgroup.coe_mul, Units.val_mul, hu, hL]
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem eq_uM_colv_mul_levi (n : ℕ) (p : Mir k n) :
    p = uM k n (GlobalTheory.CompanionTheory.MirLevi.colv p) * levi k n (mirabolicProjection k n p) := by
  have hl (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j = (g : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]
  have h1 : GlobalTheory.BZMir.mirabolicProjection k n
      (p * (GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, hl, mul_inv_cancel]
  have hm : p * (levi k n (mirabolicProjection k n p))⁻¹ ∈ MirUin k n := by
    let q := p * (levi k n (mirabolicProjection k n p))⁻¹
    have hrow : ∀ j, ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
        GlobalTheory.BZMir.eLast k n j :=
      fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (q : GL (Fin (n + 1)) k)).1 q.2) j
    have hblock : ∀ i j : Fin n,
        ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
          (1 : Matrix (Fin n) (Fin n) k) i j :=
      fun i j => congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h1
    change q ∈ MirUin k n
    rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU, MonoidHom.mem_range]
    refine ⟨Multiplicative.ofAdd fun i =>
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
    apply Units.ext
    ext i j
    change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
    rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
    · simp [Matrix.one_apply, Fin.castSucc_ne_last]
    · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow, GlobalTheory.BZMir.eLast]
    · simp [hrow, GlobalTheory.BZMir.eLast]
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k n hm
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y *
      GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p) := by
    rw [← hy, inv_mul_cancel_right]
  have hy' : GlobalTheory.CompanionTheory.MirLevi.colv p = y := by
    rw [hp]
    exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi n y _
  rw [hy']
  exact hp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colv (n : ℕ) : Continuous (GlobalTheory.CompanionTheory.MirLevi.colv : Mir k n → Fin n → k) := by
  show Continuous fun p : GlobalTheory.BZMir.Mir k n => fun i : Fin n =>
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)
  first
  | exact continuous_pi fun i =>
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)
  | exact continuous_pi fun i => (continuous_apply (Fin.last n)).comp
      ((continuous_apply (Fin.castSucc i)).comp (Units.continuous_val.comp continuous_subtype_val))
  | fun_prop

theorem coe_Bgrp_eq (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      GlobalTheory.CompanionTheory.MirLevi.colv ⁻¹' (latt n c : Set (Fin n → k)) ∩ mirabolicProjection k n ⁻¹' (K₁ : Set (GL (Fin n) k)) := by
  have hl (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j = (g : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]
  have hu (y : Fin n → k) : mirabolicProjection k n (uM k n y) = 1 := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (1 + GlobalTheory.BZMir.colMat k n y) i j = (1 : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔
    (GlobalTheory.CompanionTheory.MirLevi.colv p ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c ∧ GlobalTheory.BZMir.mirabolicProjection k n p ∈ K₁)
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · rwa [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi]
    · rwa [map_mul, hu, hl, one_mul]
  · rintro ⟨hy, hb⟩
    exact ⟨_, hy, _, hb, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.eq_uM_colv_mul_levi n p⟩

theorem coe_Bgrp_eq_image (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      (fun q : (Fin n → k) × GL (Fin n) k => uM k n q.1 * levi k n q.2) ''
        ((latt n c : Set (Fin n → k)) ×ˢ (K₁ : Set (GL (Fin n) k))) := by
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔ _
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨(y, b), ⟨hy, hb⟩, rfl⟩
  · rintro ⟨⟨y, b⟩, ⟨hy, hb⟩, rfl⟩
    exact ⟨y, hy, b, hb, rfl⟩

theorem isOpen_isCompact_Bgrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k))
    (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) →
    IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧
      IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  intro k _ _ _ _ n c K₁ h hK
  have hc : Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
    refine ⟨GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n, GlobalTheory.CompanionTheory.BZPsiPG.Cont.continuous_uM k n, ?_⟩
    have hval : Continuous fun g : Mir k n =>
        ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      Units.continuous_val.comp continuous_subtype_val
    have hblock : Continuous fun g : Mir k n =>
        ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact (continuous_apply (Fin.castSucc j)).comp ((continuous_apply (Fin.castSucc i)).comp hval)
    refine Units.continuous_iff.2 ⟨hblock, ?_⟩
    have heq : (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
        fun g => ((mirabolicProjection k n g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      funext g
      rw [map_inv]
    show Continuous (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    rw [heq]
    exact hblock.comp continuous_inv
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq]
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c).preimage (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.continuous_colv n)).inter
      (hK.preimage hc.2.2)
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq_image]
    have hK₁ : IsCompact (K₁ : Set (GL (Fin n) k)) :=
      (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).of_isClosed_subset
        (K₁.isClosed_of_isOpen hK) (SetLike.coe_subset_coe.mpr h)
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isCompact_latt n c).prod hK₁).image
      ((hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd))

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
