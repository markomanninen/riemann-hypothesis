module

public import Mathlib
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.GelfandTransference.EnergyIdentity
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.Statement

@[expose] public section

open Finset MeasureTheory NumberField
open scoped ComplexOrder

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

open Formalism.NuclearRankWeightBounds.D (lead hs q0)

def decExp (h : ℝ) (q : ℕ) (t : ℝ) : ℝ := h / 8 * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ)))

def Ydat (n f : ℕ) (rd g b : ℝ) : ℝ := (n : ℝ) * f * rd * g * b

def epsN (c : ℝ) (n f : ℕ) : ℝ := c / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)


end Formalism.HermitianLatticeCounting.S7
