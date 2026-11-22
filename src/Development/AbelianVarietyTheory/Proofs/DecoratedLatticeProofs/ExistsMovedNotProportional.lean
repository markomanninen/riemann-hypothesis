module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw

namespace GlobalTheory.PlaceCompare.Spherical

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_unram_char (D : D7) (n : ℕ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n ∧ UnramEverywhere D χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, ⟨h3.1, fun e he a => ?_⟩, fun x a b c => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]
  · rw [MonoidHom.pow_apply, h2 x a b c, one_pow]

end Global

end GlobalTheory.PlaceCompare.Spherical

end
