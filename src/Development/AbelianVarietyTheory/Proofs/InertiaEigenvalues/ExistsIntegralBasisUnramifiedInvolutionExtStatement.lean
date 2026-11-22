module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralBasisUnramifiedInvolutionExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    letI : Algebra K.E K'.E := φ.toAlgebra
    ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E,
      (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
  intro K K' d φ h hd
  let : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, key⟩ := exists_key h
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax (a : Fin d → K.E) : ∃ m, ∀ k, adicVal K (a k) ≤ adicVal K (a m) :=
    Finite.exists_max (fun k => adicVal K (a k))
  have hli : LinearIndependent K.E w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨m, hm⟩ := hmax g
    have hk := key g m hm
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hg
    rw [hg, map_zero] at hk
    have hgm : g m = 0 := (Valuation.zero_iff _).1 hk.symm
    intro k
    have hkm := hm k
    rw [hgm, map_zero] at hkm
    exact (Valuation.zero_iff _).1 (le_antisymm hkm zero_le)
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin]
    exact h.2.2.2.2.symm)
  refine ⟨B, fun z => ?_⟩
  have hz : ∑ k, φ (B.repr z k) * w k = z := by
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  obtain ⟨m, hm⟩ := hmax (B.repr z)
  have hv := key _ m hm
  rw [hz] at hv
  rw [← adicVal_le_one_iff K' z]
  constructor
  · intro hzO k
    rw [← adicVal_le_one_iff]
    exact (hm k).trans (hv ▸ hzO)
  · intro hall
    rw [hv]
    exact (adicVal_le_one_iff K _).2 (hall m)
