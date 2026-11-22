module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceDegree

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pAutEx_of :
    UpperTheory.Gal.CertificateRingHomMap.AutEx := by
  intro E _ _ τ τ₀
  obtain ⟨σ, hσ⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegreeAlt.exists_ringEquiv_comp τ τ₀
  exact ⟨σ, fun y => RingHom.congr_fun hσ y⟩
