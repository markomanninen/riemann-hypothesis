module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompatibleOfSameSplittingCharacter
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCompatible_of_sameSplittingCharacter : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.CompatibleOfSameChar D := by
  first | exact @GlobalTheory.SameCharCompat.compatibleOfSameChar | exact GlobalTheory.SameCharCompat.compatibleOfSameChar | (intros; apply GlobalTheory.SameCharCompat.compatibleOfSameChar <;> assumption)
