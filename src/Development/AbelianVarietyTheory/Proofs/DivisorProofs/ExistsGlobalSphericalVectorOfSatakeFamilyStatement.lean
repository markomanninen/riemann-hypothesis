module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSphericalVectorOfSatakeFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_spherical_vector_of_satake_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ), (∀ w ∉ S, GlobalTheory.LFun.HasSatGL w (π.locRep w) (B w)) → ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), act (.fin (locGL E a w k)) φ = φ := by
  first | exact @GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat | exact GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat | (intros; apply GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat <;> assumption)
