module

public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinTorusVanishing

open Ad3 Ad3.R

section Mat

variable {R : Type*} [CommRing R]

end Mat

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

end Loc

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {ψ : AddChar F Circle} {ω : Fˣ →* ℂˣ} {lam : ℂ} {W : GL (Fin 2) F → ℂ}

end Main

end GlobalTheory.CompanionTheory.RankinTorusVanishing

end
