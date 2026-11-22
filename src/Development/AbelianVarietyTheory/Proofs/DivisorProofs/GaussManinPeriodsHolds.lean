module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoGStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PTaylor0

@[expose] public section

open GlobalTheory.AnPer

namespace GlobalTheory.PeriodFamily

theorem gaussManinPeriods_holds : GlobalTheory.Published.GaussManinPeriods :=
  gaussManinPeriods_of_span_taylor GlobalTheory.T.periods_span_deRhamHomology_rank_two_g
    GlobalTheory.AnPer.TaylorClause.pTaylor0

end GlobalTheory.PeriodFamily
