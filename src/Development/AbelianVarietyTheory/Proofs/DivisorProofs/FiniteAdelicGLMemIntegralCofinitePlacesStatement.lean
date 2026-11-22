module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)), {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite := by
  first | exact @GlobalTheory.GLFinPlaces.gl_mem_int_cofinite | exact GlobalTheory.GLFinPlaces.gl_mem_int_cofinite | (intros; apply GlobalTheory.GLFinPlaces.gl_mem_int_cofinite <;> assumption)
