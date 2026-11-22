module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGeneratorPlaceValuationBound_proof : ShortBoundSt := by
  first | exact @GlobalTheory.ShortBound.shortBound | exact GlobalTheory.ShortBound.shortBound | (intros; apply GlobalTheory.ShortBound.shortBound <;> assumption)
