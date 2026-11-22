module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTnScalarUniformiserSingleTranslation
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

@[expose] public section

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)), ∃ g, GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  first | exact @GlobalTheory.LFun.tn_single | exact GlobalTheory.LFun.tn_single | (intros; apply GlobalTheory.LFun.tn_single <;> assumption)
