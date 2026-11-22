module

public import Formalism.GaussJetBounds.StatementN
public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

section Analytic

variable {K : Type u} [Field K] {ι : Type} [Fintype ι]

def dirD (L : ι → K) : Derivation K (MvPowerSeries ι K) (MvPowerSeries ι K) :=
  ∑ x, L x • MvPowerSeries.pderiv (R := K) x

end Analytic

section Exp

variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]

lemma constantCoeff_mvExp (f : MvPowerSeries ι K) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  unfold mvExp
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hf, hn]

end Exp

section Comb

variable {n : ℕ}

variable {R : Type u} [CommRing R]

end Comb

section Main

variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]

end Main

end Formalism.DworkPowerSeriesWeights
