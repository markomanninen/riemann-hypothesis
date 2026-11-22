module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.LinkDef
public import Formalism.AdicCompletionExports.NonnegativeDivisors.Imports
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.MainNotions Formalism.AdicCompletionExports.NonnegativeDivisors

section Rec

variable {D : D7}

theorem zero_le_logWeight (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  unfold SizeData₂.lwP Formalism.BasicNotions.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

def TieTwRec (L : SizeData₂ D) (Tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop :=
  ∀ y ∈ Tw, D.plEq.symm y ∈ L.supp ∧ D.what₂.muAt (D.plEq.symm y) ≠ D.what₂.mu0

end Rec

section Ties

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  (F : DefFam D.what₂.LL G Pl0 T (Fin D.R.m)) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub F.amb)
  (μ : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (Tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)))

end Ties

section Inputs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

variable {A : FamIn K G Pl0 T m} {s : ℕ} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {C CH : ℝ} {Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH}
  {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : RecNums A.fam.base.J Pl} {u : (Dc Pk.Zs).Mem}
  {Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ} {bd : A.fam.base.J → ℝ}

end Inputs

end Formalism.L2.DIV
