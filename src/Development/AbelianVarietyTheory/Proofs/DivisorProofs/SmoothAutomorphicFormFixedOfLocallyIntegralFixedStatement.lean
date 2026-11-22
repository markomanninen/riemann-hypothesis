module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixed
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) → (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  first | exact @GlobalTheory.CuspRep.fixed_of_locFixed | exact GlobalTheory.CuspRep.fixed_of_locFixed | (intros; apply GlobalTheory.CuspRep.fixed_of_locFixed <;> assumption)
