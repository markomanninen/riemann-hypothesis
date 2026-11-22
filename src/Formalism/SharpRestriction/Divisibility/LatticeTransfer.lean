module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.DegreeFormula.FlagDegFormula
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.Divisibility.PrinLevClass

@[expose] public section

noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

structure Loc (D : D7) (XD : DivX D) where

  rt : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev) (p : ℕ) [Fact p.Prime]
    (la : XD.PlP p) (z : XD.Mp S κ p la), Bool × Rt D.what₂.Tau (XD.shv S κ).N → (XD.md S κ p la z).Z.LB

  rt_lie : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ)) (i' : Fin (XD.shv S κ).N),
      (i' : ℕ) = i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).lie τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).lie τ).x' i

  rt_om : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
      (i' : Fin (XD.shv S κ).N), (i' : ℕ) = (XD.shv S κ).j + i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).om τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).om τ).x' i

  lieW_gen : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la), ∃ (e : Fin (D.R.f * (XD.shv S κ).N) ≃ Rt D.what₂.Tau (XD.shv S κ).N)
      (V : Fin (D.R.f * (XD.shv S κ).N) → (XD.md S κ p la z).Z.VDiv), ∀ l,
      (XD.md S κ p la z).Z.c1 ((XD.md S κ p la z).lieW.x l) =
        (if ((e l).2 : ℕ) < (XD.shv S κ).j then (1 : ℚ) else -1) •
            (XD.md S κ p la z).Z.c1 (rt S κ p la z (false, e l)) +
          (XD.md S κ p la z).Z.cD (V l)

section One
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def adm1 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ c : (XD.shv S κ).FibComp p, ¬ (XD.shv S κ).fibInBd p c

end One

def PointsLemma (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p
        ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            collapse D _ Q)) -
        (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (Sum.inl τ) * collapse D _ Q) /
          ((p : ℝ) - 1))

section One1
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

end One1

end Formalism.MainNotions.LatticeTransfer

end
