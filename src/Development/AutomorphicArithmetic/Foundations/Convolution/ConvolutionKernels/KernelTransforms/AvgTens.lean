module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.avgTens :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n) (Φ : AdelicGLn.AdelicGL K n → ℂ),
      (∀ g, Φ g = β (infPart K n g) * e (finPart K n g)) →
      (∀ x, PositivityTheory.Rg.Tf.Geo.avg Φ x = tens β e x) ∧
      ∀ g : AdelicGLn.AdelicGL K n, archEquiv K n (PositivityTheory.Rg.Tf.Geo.mapGL n (RingHom.fst _ _) g) = infPart K n g := by
  intro K _ _ n hn β e Φ hΦ
  refine ⟨fun x => ?_, fun g => ?_⟩
  · have hemb : MeasurableEmbedding GroundTheory.Global.expPos :=
      GroundTheory.Global.expPosHomeomorph.measurableEmbedding
    have ht : tens β e x = tensFun β e x := by
      have h1 : Continuous (tensFun β e) := by
        unfold tensFun
        exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
          (continuous_infPart.comp continuous_subtype_val)).mul
          (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
      have hfin : Continuous (MultiplicityOne.finProj (K := K) (n := n)) :=
        continuous_retractOne.comp continuous_finEmb
      have hfinC : IsCompact (MultiplicityOne.finProj (K := K) (n := n) '' tsupport e) :=
        e.hasCompactSupport.isCompact.image hfin
      have harchC : IsCompact (archP K n '' tsupport β) :=
        β.hasCompactSupport.isCompact.image continuous_archP
      have hC : IsCompact (archP K n '' tsupport β * MultiplicityOne.finProj (K := K) (n := n) '' tsupport e) :=
        harchC.mul hfinC
      have hS : Function.support (tensFun β e) ⊆
          archP K n '' tsupport β * MultiplicityOne.finProj (K := K) (n := n) '' tsupport e := by
        intro y hy
        let a := infPart K n (y : AdelicGLn.AdelicGL K n)
        let h := finPart K n (y : AdelicGLn.AdelicGL K n)
        change kbar β a * e h ≠ 0 at hy
        have he := right_ne_zero_of_mul hy
        obtain ⟨s, hs⟩ : ∃ s, β (a * zInf K n s) ≠ 0 := by
          by_contra h0
          simp only [not_exists, ne_eq, not_not] at h0
          exact left_ne_zero_of_mul hy (by simp [kbar, h0])
        have hproj : archP K n (a * zInf K n s) * MultiplicityOne.finProj (K := K) (n := n) h = y := by
          have hf : MultiplicityOne.finProj (K := K) (n := n) h = retractOne (finEmb K n h) := rfl
          rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul]
          change retractOne (infEmb K n (infPart K n (y : AdelicGLn.AdelicGL K n)) *
            finEmb K n (finPart K n (y : AdelicGLn.AdelicGL K n))) = y
          rw [infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
        rw [← hproj]
        exact Set.mul_mem_mul ⟨_, subset_tsupport _ hs, rfl⟩ ⟨_, subset_tsupport _ he, rfl⟩
      have h2 : HasCompactSupport (tensFun β e) :=
        hC.of_isClosed_subset isClosed_closure (closure_minimal hS hC.isClosed)
      have h : Continuous (tensFun β e) ∧ HasCompactSupport (tensFun β e) := ⟨h1, h2⟩
      rw [tens, dite_eq_left h]
      rfl
    rw [ht, tensFun, kbar, GroundTheory.Global.posRealMeasure_eq_map_expPos,
      hemb.integral_map, ← integral_mul_const]
    unfold PositivityTheory.Rg.Tf.Geo.avg
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have h1 : infPart K n (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) =
        infPart K n (x : AdelicGLn.AdelicGL K n) * zInf K n (GroundTheory.Global.expPos t) := by
      rw [map_mul (infPart K n), ← zInf_mul_comm]
      rfl
    have h2 : CuspidalSpectrum.finPart K n (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) =
        CuspidalSpectrum.finPart K n (x : AdelicGLn.AdelicGL K n) := by
      rw [map_mul (CuspidalSpectrum.finPart K n), finPart_centralSection, one_mul]
    change Φ (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) = _
    rw [hΦ, h1, h2]
  · rw [infPart_apply]
    rfl
