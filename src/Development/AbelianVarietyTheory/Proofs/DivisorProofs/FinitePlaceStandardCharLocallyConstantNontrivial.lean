module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW

theorem psiLoc_addChar_locallyConstant_ne_one :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ,
      (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  intro E _ _ w
  refine ⟨psiLocChar w, fun x => rfl, ?_, ?_⟩
  · have hc : Continuous (psiLocChar w) := by
      have : (psiLocChar w : w.adicCompletion E → ℂ) = fun x => ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) := by
        funext x; exact GlobalTheory.JSW.WhitModel.psiLoc_eq w x
      rw [this]
      exact continuous_subtype_val.comp (GroundTheory.Global.continuous_localAdelicChar w)
    exact GlobalTheory.SchrSBFin.isLocallyConstant_addChar _ hc
  · intro h
    apply GroundTheory.Global.localAdelicChar_ne_one (K := E) (v := w)
    refine AddChar.ext _ _ fun x => ?_
    have h1 : psiLocChar w x = 1 := by rw [h]; rfl
    have h2 : ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) = 1 := by
      rw [← GlobalTheory.JSW.WhitModel.psiLoc_eq]; exact h1
    exact Subtype.ext h2

end GlobalTheory.JSW
