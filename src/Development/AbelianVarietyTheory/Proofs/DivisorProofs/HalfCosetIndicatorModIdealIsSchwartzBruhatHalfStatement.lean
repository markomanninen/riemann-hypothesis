module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfCosetIndicatorModIdealIsSchwartzBruhatHalf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfCosetIndicatorModIdeal_isSchwartzBruhatHalf : ∀ {D : D7} (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (a : Formalism.L2.Theta.AE D), infPart D a = 0 →
    ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ x : WO S T, IsHalf a x → IsSBHalf a (latO S T LS LT fun _ => True) (cosetFn a I x) := by
  first
  | exact @GlobalTheory.BotSmallDict.cosetFn_isSBHalf
  | intro D S T LS LT hS hT a ha I hI x hx
    exact GlobalTheory.BotSmallDict.cosetFn_isSBHalf S T LS LT hS.toIsLattice hT.toIsLattice a ha I hI x hx
