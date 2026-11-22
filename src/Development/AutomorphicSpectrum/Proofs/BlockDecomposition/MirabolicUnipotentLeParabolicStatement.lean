module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentLeParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_le_parabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (m j : ℕ),
      MirUin k (m + j) ≤ GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
  intro k _ _ _ _ m j g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  change (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro x y b a hxy
  obtain ⟨rfl, rfl⟩ := Bool.lt_iff.mp hxy
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  have hne : eGP m j ⟨true, b⟩ ≠ eGP m j ⟨false, a⟩ := by
    intro h
    have hval := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val,
      GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val] at hval
    have ha := a.isLt
    omega
  rw [hmat]
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat,
    ite_eq_right (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a), ite_eq_right hne,
    add_zero]
