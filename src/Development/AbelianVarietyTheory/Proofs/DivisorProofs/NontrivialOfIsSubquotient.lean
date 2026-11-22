module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

@[expose] public section

open GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.TypeTwo.PowIrrProof

theorem equiv_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
    (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  letI : ρ.IsIrreducible := hρ
  rcases eq_bot_or_eq_top S with rfl | rfl
  · obtain ⟨v, rfl⟩ := hf y
    have hv : v = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 v.property)
    exact (hy (by rw [hv, map_zero])).elim
  · let e := (topEquiv ρ).symm
    let F : ρ.IntertwiningMap σ := f.comp e.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp e.toLinearEquiv.surjective
    have hi : Function.Injective F :=
      (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right fun hF => by
        obtain ⟨x, hx⟩ := hs y
        exact hy (by simpa [hF] using hx.symm)
    exact ⟨F.ofBijective ⟨hi, hs⟩⟩

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W] :
    Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  letI : Nontrivial S.toSubmodule := hf.nontrivial
  exact Subtype.val_injective.nontrivial (α := S.toSubmodule)

end GlobalTheory.TypeTwo.PowIrrProof
