module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteAutomorphicRepGL_exists_localComponent : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  first | exact @GlobalTheory.DiscLocEx.exists_isLocCompGL | exact GlobalTheory.DiscLocEx.exists_isLocCompGL | (intros; apply GlobalTheory.DiscLocEx.exists_isLocCompGL <;> assumption)
