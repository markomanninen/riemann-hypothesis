module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.Foundations.VanishOrdL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocPublishedOfLitCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrdinaryNormalFormUnramifiedSourceStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem repIso_symm_srcL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W W' : R2 Ω l}
    (h : RepIso W W') : RepIso W' W := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, fun s => ?_⟩
  rw [hg s]
  group

theorem vanishOrdL_of_zetaUr : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ZetaUr → VanishOrdL := by
  intro hC hZ l _ hl Ω _ _ _ ι e he W hW hS
  obtain ⟨S, A, W', g, hiso, hnf, hsrc⟩ := GlobalTheory.T.exists_ordinary_normal_form_unramified_source l Ω ι e W hl he hW hS
  have hes : ES W' A := hZ l Ω ι e S A W' g hnf hsrc
  have hv : BlochKatoSelmerVanishes l (Loc.colRep W') := GlobalTheory.Ord2.es_vanish hC l Ω e S A W' hnf hes
  exact UpperTheory.V.X.Kato.conj l ℚ Ω 2 W' W (repIso_symm_srcL hiso) hv

end GlobalTheory.Ord2
