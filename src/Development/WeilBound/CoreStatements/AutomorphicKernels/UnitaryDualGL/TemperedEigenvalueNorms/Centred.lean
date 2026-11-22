module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace PositivityTheory.UdReth2

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsCentred (Δ : Segment k) : Prop :=
  ∀ ω : kˣ →* ℂˣ, HasCentralChar Δ.first.rep ω → ∀ z : kˣ,
    Real.log ‖(ω z : ℂ)‖ = -((Δ.d : ℝ) * ((Δ.len : ℝ) - 1) / 2) * Real.log (nabs k z)

end Local

end PositivityTheory.UdReth2
