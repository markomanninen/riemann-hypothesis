module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → ∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1 := by
  first | exact @GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne | exact GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne | (intros; apply GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne <;> assumption)
