module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisation
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspParam_of_greenParametrisation : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam (ZMod g) (convC t ht ζ hζ) := by
  first | exact @GlobalTheory.GreenParam.cuspParam_of_green | exact GlobalTheory.GreenParam.cuspParam_of_green | (intros; apply GlobalTheory.GreenParam.cuspParam_of_green <;> assumption)
