module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV

@[reducible] def fieldsOf (D : D7) : Fields where
  F := D.host.F
  E := D.host.E
  K := D.what₂.LL
  starE := D.host.cmStar
  Tau := D.what₂.Tau
  deTau := Classical.decEq _
  emb τ := D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

@[reducible] def primesOf (D : D7) (EX : ErrX D) : Primes (fieldsOf D) where
  cond := D.host.QS * D.host.q * D.host.d
  g := D.host.g
  piG := EX.piG
  Word := D.what₂.Word
  ftWord := D.wordFin
  deWord := Classical.decEq _
  T u := (D.mem u).A.T
  piT := EX.piT

def seamOf (D : D7) : Seam D (fieldsOf D) where
  iE := RingEquiv.refl _
  iT := Equiv.refl _
  σ₀ := D.what₂.embLL

section Ties

variable (D : D7) (Dx : DivX D) (EX : ErrX D) (Ch : Chars (fieldsOf D) (primesOf D EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 (fieldsOf D).F) → HeightOneSpectrum (𝓞 (fieldsOf D).E))

variable {S : Set ℕ} (ξ : Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S)

end Ties

def Bound (D : D7) (L : SizeData₂ D) (EX : ErrX D) (C1 : ℝ) (i : Fin 2) (w : LiftErrorLocal.Pl D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier,
    ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
      (y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y)

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

end
