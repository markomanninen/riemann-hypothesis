module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigMap
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open UpperTheory.V.Af.Smo (Eig)

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfEig :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfEig F := by
  intro F _ _ f hf v B h g
  let W (b : A F) (y : GL (Fin 2) (v.adicCompletion F)) :=
    f (gl (nU b) * (g * finGL F 2 (locGL F 2 v y)))
  have hW (b : A F) : Eig v B (W b) := by
    simpa only [W, mul_assoc] using h (gl (nU b) * g)
  have hi (y : GL (Fin 2) (v.adicCompletion F)) :
      IntegrableOn (fun b => W b y * ψ b) (fundamentalSet F) (adeleMeasure F) :=
    intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  change Eig v B (fun y => ∫ b in fundamentalSet F, W b y * ψ b ∂(adeleMeasure F))
  refine ⟨(h 1).card, fun y k hk => by simp only [fun b => (hW b).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hsupp := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm F v 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hsum (G : GL (Fin 2) (v.adicCompletion F) ⧸ GlobalTheory.LFun.KGL v (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c =
        ∑ c ∈ hsupp.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hsum]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have hb := (hW b).eig ϖ hϖ j hj y
  rw [hsum] at hb
  simp only [← mul_assoc, ← hb, Finset.sum_mul]
