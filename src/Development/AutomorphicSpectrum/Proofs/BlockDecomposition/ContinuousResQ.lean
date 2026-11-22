module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def resQ (φ : GA E a → ℂ) : RightCosetSpace (rationalGLOne (K := E) (n := a)) → ℂ :=
  fun q => φ ((Quotient.out q : normOneGL (K := E) (n := a)) : GA E a)

theorem resQ_mk {φ : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) (x : normOneGL (K := E) (n := a)) :
    resQ φ (RightCosetSpace.mk _ x) = φ x := by
  have e : RightCosetSpace.mk (rationalGLOne (K := E) (n := a))
      (Quotient.out (RightCosetSpace.mk (rationalGLOne (K := E) (n := a)) x)) = RightCosetSpace.mk _ x :=
    Quotient.out_eq _
  obtain ⟨γ, hγ⟩ := RightCosetSpace.mk_eq_mk_iff.1 e
  obtain ⟨δ, hδ⟩ : ((γ : normOneGL (K := E) (n := a)) : GA E a) ∈ AdelicGLn.rationalGL E a := γ.2
  unfold resQ
  rw [← hγ]
  change φ (((γ : normOneGL (K := E) (n := a)) : GA E a) * (x : GA E a)) = _
  rw [← hδ]
  exact h δ x.1

theorem continuous_resQ {φ : GA E a → ℂ} (hc : Continuous φ) (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) :
    Continuous (resQ φ) := by
  refine (RightCosetSpace.isOpenQuotientMap_mk (rationalGLOne (K := E) (n := a))).isQuotientMap.continuous_iff.2 ?_
  have : resQ φ ∘ RightCosetSpace.mk (rationalGLOne (K := E) (n := a)) = fun x : normOneGL (K := E) (n := a) => φ x :=
    funext fun x => resQ_mk h x
  rw [this]
  exact hc.comp continuous_subtype_val

end GlobalTheory.CompanionTheory.CuspTransfer
end
