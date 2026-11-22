module

public import Mathlib
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.ThDistC

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Frames

variable (D : D7) {N : ℕ} {Y : Type} (frm : Y → D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)

end Frames

structure ChainData (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  X : Fields
  s : Seam D X
  Pr : Primes X

  w : Pr.Word
  Ch : Chars X Pr D.R.m

  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)
  S : Set ℕ

  xi : Tup X.F X.E X.K S
  cst : LocCst X (rowSG Pr sel xi)
  L : ChIdx X Pr D.R (QE sel (xi : Chr X.F X.E X.K))
  G : ChGlob X D.R.m
  δ : ℂ
  B : Base D D.host.ccK δ
  idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D
  O : GL3Theta.LiftObj D (D.chTw u μ)

  lamTop : rowSG Pr sel xi → Submodule (𝓞 X.E) (Sp X.E (D.R.N D.R.m - 1 + 0))

  depth : rowSG Pr sel xi → ℕ

  rep : ∀ i, (D.chTw u μ).cls i →
    Option (L.β i) × DecoF X.E (D.R.N i) (Pr.vT w) ∅ (rowSG Pr sel xi) × Set (Sp X.E (D.R.N i))

namespace ChainData

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)





end ChainData

end GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData
