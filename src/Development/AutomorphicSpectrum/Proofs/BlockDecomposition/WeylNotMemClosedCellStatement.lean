module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylNotMemClosedCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_not_mem_closed_cell :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (i t : ℕ),
      GlobalTheory.CompanionTheory.BZPhiPG.wEl (k := k) i t ∉ Cl (k := k) i t ∧
        dEmb (k := k) i t 0 = 1 := by
  intro k _ _ _ _ i t
  constructor
  · intro hmem
    simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_ofPred_eq] at hmem
    let c : Fin ((i + 1) + t + 1) := ⟨i, by omega⟩
    have hc : (Fin.castLE (by omega) (Fin.last i) : Fin ((i + 1) + t + 2)) =
        Fin.castSucc c := Fin.ext rfl
    have hzero := hmem (Fin.last i)
    rw [hc, GlobalTheory.CompanionTheory.BZPhiPG.wEl, ← map_inv] at hzero
    change GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
        (((wGL (k := k) i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
          Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 0 at hzero
    simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc] at hzero
    change Equiv.Perm.permMatrix k (piPerm i t) (Fin.last ((i + 1) + t)) c = 0 at hzero
    have hperm : piPerm i t (Fin.last ((i + 1) + t)) = c :=
      Fin.ext (piPerm_last_val i t)
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hperm] at hzero
  · have h : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
      funext j
      refine Fin.addCases (fun a => ?_) (fun b => ?_) j
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]; rfl
    apply Subtype.ext
    change GlobalTheory.BZMir.unip k ((i + 1) + (t + 1))
      (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k))) = 1
    rw [h, ofAdd_zero, map_one]
