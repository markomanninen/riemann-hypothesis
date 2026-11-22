module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.JacCols

theorem cols_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * F.β r' m = 0 := by
  intro D k _ _ _ _ p ρ J n _ _ c s hh F₀ F hF i
  obtain ⟨hc, h0, h1, h2⟩ := hF
  subst hc
  have hpr : ∀ a, p.pr a = Witness.prH p a := fun _ => rfl

  have hG : (J.W.gram)ᴴ = J.W.gram := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.gram_star J.W b a

  have L : ∀ {Z : Type} [Fintype Z] (M : Matrix (Fin J.W.rank) Z k) (z : Z),
      ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * M r' z =
        (((J.d.eᴴ * J.W.gram).map (Witness.prH p)) * M) i z := by
    intro Z _ M z
    rw [Finset.sum_comm, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r' _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, Matrix.map_apply, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, Matrix.conjTranspose_apply, hpr, hpr]
  have Ls : ∀ (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ) (t : k),
      ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * (t * p.pr (M r' j)) =
        t * Witness.prH p ((J.d.eᴴ * J.W.gram * M) i j) := by
    intro M j t
    have := L (t • M.map (Witness.prH p)) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    simp only [hpr] at this ⊢
    rw [this, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, ← Matrix.map_mul]
    rfl

  have eI : J.d.eᴴ * J.W.gram * J.d.i₀ = 0 := by
    have := congrArg Matrix.conjTranspose J.d.i₀e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this
  have eE' : J.d.eᴴ * J.W.gram * J.d.e' = 1 := by
    have := congrArg Matrix.conjTranspose J.d.e'e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc] at this
  refine ⟨Sum.inr ⟨i.val, by omega⟩, Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, fun r => h1 i _ rfl r,
    fun r => h2 i _ (by simp only; omega) r, ?_⟩
  intro m hm
  rcases m with a | ⟨j, hj⟩
  · rw [L F.β (Sum.inl a)]
    have hcol : ∀ r, F.β r (Sum.inl a) = (J.d.i₀.map (Witness.prH p) * F₀.β) r a := fun r => h0 r a
    rw [Matrix.mul_apply]
    simp only [hcol]
    rw [← Matrix.mul_apply, ← Matrix.mul_assoc, ← Matrix.map_mul, eI, Matrix.map_zero _ (map_zero _), Matrix.zero_mul,
      Matrix.zero_apply]
  · by_cases hjρ : j < ρ
    · have hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * p.xi ^ (ρ - j) * p.pr (J.d.e r ⟨j, hjρ⟩) :=
        fun r => h1 ⟨j, hjρ⟩ _ rfl r
      simp only [hcol]
      rw [Ls, J.d.ee, Matrix.zero_apply, map_zero, mul_zero]
    · set i' : Fin ρ := ⟨2 * ρ - 1 - j, by omega⟩ with hi'
      have hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i'.val) * p.pr (J.d.e' r i') :=
        fun r => h2 i' _ (by simp only [hi']; omega) r
      simp only [hcol]
      have hne : i ≠ i' := by
        intro h
        apply hm
        rw [h]
        simp only [hi', Sum.inr.injEq, Fin.mk.injEq]
        omega
      rw [Ls, eE', Matrix.one_apply_ne hne, map_zero, mul_zero]

end GlobalTheory.LocMod.JacCols
