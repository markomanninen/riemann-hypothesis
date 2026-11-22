module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKtypeCoefficientExplicitPowerDecay
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay : DecPow := by
  first | exact @GlobalTheory.SepReal.decPow | exact GlobalTheory.SepReal.decPow | (intros; apply GlobalTheory.SepReal.decPow <;> assumption)
