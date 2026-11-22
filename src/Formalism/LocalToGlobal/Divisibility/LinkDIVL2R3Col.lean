module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef

section Face

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem linkDIV_L2R_face [_root_.NumberField.IsTotallyComplex K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (Pk : IndefPkgR A fc cf C CH) (wf0 : (fc Pk.Zs).Df0.WF) (wf1 : (fc Pk.Zs).Df1.WF)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (u : (fc Pk.Zs).Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin ((fc Pk.Zs).Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputsR Pk.core R u Nu sg) : DivClausesR Pk.core R u Nu sg :=
  divClausesR_of wf0 wf1 Pk.core R u Nu sg I

end Face

section Fam3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

end Fam3

section Col3

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)

end Col3

end Formalism.L2.DIV
