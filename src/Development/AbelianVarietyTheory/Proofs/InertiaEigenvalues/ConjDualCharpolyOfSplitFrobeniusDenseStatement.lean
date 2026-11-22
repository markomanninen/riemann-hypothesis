module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDense
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i), FrobDual i s → CharDual i s := by
  first | exact @GlobalTheory.CharDualDense.charDual_of_frobDual | exact GlobalTheory.CharDualDense.charDual_of_frobDual | (intros; apply GlobalTheory.CharDualDense.charDual_of_frobDual <;> assumption)
