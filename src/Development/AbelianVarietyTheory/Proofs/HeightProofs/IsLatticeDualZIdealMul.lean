module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.LocalRingCardinality.SpanPowerMembership.Places
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataParamsT
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TotallyPositiveExponents

@[expose] public section

open NumberField Matrix Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

namespace GlobalTheory.CuspCharLattice

section General

variable {K : Type} [Field K] [NumberField K]

end General

variable {R : Ranks} {H : Host R} {n : ℕ}

theorem host_AA_ne_zero (H : Host R) : H.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact H.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := H.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

end GlobalTheory.CuspCharLattice
