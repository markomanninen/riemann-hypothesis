module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (Eig EigAt)
open scoped ComplexOrder

theorem UpperTheory.eigAt_cmDatumOperator_of_eigAt :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (w : H.P E) (B : Multiset ℂˣ), Continuous φ → EigAt w B φ → EigAt w B (Wo D φ) := by
  intro E _ _ D φ w B hφ hB g
  have hnE : Continuous (nE D) := by
    have hmkE : Continuous fun x : Fin 2 → A ℚ => D.mkE (x 0) (x 1) :=
      (AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
        ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)
    exact (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp
      UpperTheory.ConvolutionTheory.R2.M.continuous_nU).comp hmkE
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have hi : ∀ h : GL (Fin 2) (A E),
      IntegrableOn (fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
    intro h
    obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
      ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
        (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
        fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
    have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
    have hc : Continuous fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1) :=
      (hφ.comp (hnE.mul continuous_const)).mul (hψ.comp (continuous_apply 1))
    exact (hc.continuousOn.integrableOn_compact hK).mono_set fun x hx i hi => hEC (hx i hi)
  let G (x : Fin 2 → A ℚ) (y : GL (Fin 2) (w.adicCompletion E)) :=
    φ (nE D x * (g * finGL E 2 (locGL E 2 w y)))
  have hG (x : Fin 2 → A ℚ) : Eig w B (G x) := by
    simpa only [G, mul_assoc] using hB (nE D x * g)
  have hGi (z : GL (Fin 2) (w.adicCompletion E)) :
      Integrable (fun x => G x z * ψ (x 1)) ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := hi _
  change Eig w B (fun y => ∫ x in FS2 ℚ, G x y * ψ (x 1) ∂(adeleMeasurePi ℚ))
  refine ⟨(hB 1).card, fun y k hk => by simp only [fun x => (hG x).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hs (f : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * f c =
        ∑ c ∈ hf.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * f c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hGi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (hG x).eig ϖ hϖ j hj y
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]
