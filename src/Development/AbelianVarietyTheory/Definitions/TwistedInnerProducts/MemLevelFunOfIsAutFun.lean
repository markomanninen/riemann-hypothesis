module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil
open GlobalTheory.AdelicU (splitProj compFin splitEquiv splitEquivIn splitHom isCMExt_host)
open GlobalTheory.EmbChart (tensAt atPlace idem)
open GlobalTheory.StepData (LatFrame reGL)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocFrame

section Inst

variable {F : Type} [Field F] [NumberField F]

end Inst

section Bases

variable {k ι Y : Type} [Field k] [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

def vec (β : LatFrame k ι Y) (i : ι) : Y → k := fun y => β.bas.val y (β.ord i)





end Bases

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

def piW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D →+* Fv D.host.F v :=
  (splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (compFin D.host.F D.host.E v)

theorem chart_piW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : GlobalTheory.SplitHecke.Chart (idem τ) v (piW τ) :=
  GlobalTheory.EmbChart.chart_idem τ

theorem piW_incA (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : D.host.E) : piW τ (incA D x) = τ x := by
  change splitProj τ (GlobalTheory.AdelicU.evFin D.host.F v 1 ⊗ₜ x) = _
  rw [map_one, GlobalTheory.AdelicU.splitProj_tmul, one_mul]

section Loc

variable (V : HSp D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {ι : Type} [Fintype ι] [DecidableEq ι]
  (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

end Loc

section Rep

variable (V : HSp D)

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {ι : Type} [Fintype ι] [DecidableEq ι]
  (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

end Rep

section Position

open GlobalTheory.RootEx

variable {k : Type} [Field k] [MeasurableSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
  (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [ν.IsAddHaarMeasure]
  {ψ : AddChar k Circle} {σ}

end Position

section Positions

open GlobalTheory.RootEx

variable {I : Type} {k : I → Type} [∀ i, Field (k i)] [∀ i, MeasurableSpace (k i)] {n : Type} [Fintype n] [DecidableEq n]
  {c : ℕ} {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
  (ν : ∀ i, Measure (k i)) (σ : ∀ i, Representation ℂ (GL (n ⊕ Fin c) (k i)) A)

variable [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
  [∀ i, BorelSpace (k i)] [∀ i, (ν i).IsAddHaarMeasure] {ψ : ∀ i, AddChar (k i) Circle} {σ}

end Positions

end GlobalTheory.LocFrame

end
