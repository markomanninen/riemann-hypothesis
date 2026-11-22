module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodingerStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralActionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealMetaplecticFamilyDerivativeQuadraticStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanThetaFamilyExistsSmooth

@[expose] public section

section
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
namespace GlobalTheory.OscQuad
theorem oscillator_deriv_along_line_quadratic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (m : ℕ) (u v : Fin m → Matrix (Fin n) (Fin d) (AE F E)) (c : Fin m → ℂ) (c₀ : ℂ),
      (∀ i, At (evI F) (u i) ∧ At (evI F) (v i)) ∧
      ∀ (f : SInf F (Fin n × Fin d)) (g₁ g₂ : Fin m → SInf F (Fin n × Fin d)),
        (∀ i, ActsD (evI F) (M.heisLine ψ (v i)) f (g₁ i)) → (∀ i, ActsD (evI F) (M.heisLine ψ (u i)) (g₁ i) (g₂ i)) →
        ∀ F₁ : ℝ → SInf F (Fin n × Fin d), (∀ t, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (F₁ t)) →
        ∀ y, HasDerivAt (fun t => F₁ t y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  classical
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ
  obtain ⟨T, hT, hadd, h0⟩ := _root_.GlobalTheory.T.archimedean_theta_family_exists_smooth hP M ψ χX χW om hCM hψ hW γ hγ
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    GlobalTheory.T.weil_representation_integral_action M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.archimedeanOneParameterFamily_continuous M ψ χX χW om hW γ hγ T hT
  have trace_real {ι : Type} [Fintype ι] (f : ι → ℝ) :
      Algebra.trace ℝ (ι → ℝ) f = ∑ i, f i := by
    rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι)]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, Pi.single_apply]
  have trace_complex {ι : Type} [Fintype ι] (f : ι → ℂ) :
      Algebra.trace ℝ (ι → ℂ) f = ∑ i, 2 * (f i).re := by
    rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => Complex.basisOneI)]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, Fintype.sum_sigma, Pi.single_apply, Fin.sum_univ_two,
      Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have trace_nondeg (x : mixedEmbedding.mixedSpace F)
      (h : ∀ b, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * b) = 0) : x = 0 := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · have h1 := h (Pi.single w 1, 0)
      rw [Algebra.trace_prod_apply, trace_real, trace_complex] at h1
      simpa [Pi.single_apply] using h1
    · have h1 := h (0, Pi.single w (star (x.2 w)))
      rw [Algebra.trace_prod_apply, trace_real, trace_complex] at h1
      have h2 : (x.2 w).re * (x.2 w).re + (x.2 w).im * (x.2 w).im = 0 := by
        simpa [Pi.single_apply, apply_ite Complex.re, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.star_def,
          Complex.mul_conj] using h1
      have hre : (x.2 w).re = 0 := by nlinarith [mul_self_nonneg (x.2 w).re, mul_self_nonneg (x.2 w).im]
      have him : (x.2 w).im = 0 := by nlinarith [mul_self_nonneg (x.2 w).re, mul_self_nonneg (x.2 w).im]
      exact Complex.ext hre him
  have hpair : IsPairing (trP F (Fin n × Fin d)) := by
    exact {
      addL x x' y := by simp only [trP, Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
      addR x y y' := by simp only [trP, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
      smulL c x y := by simp only [trP, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul]
      smulR c x y := by simp only [trP, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]
      nondegL x hx := by
        funext i
        apply trace_nondeg
        intro b
        have h := hx (Pi.single i b)
        simpa [trP, Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h
      nondegR y hy := by
        funext i
        apply trace_nondeg
        intro b
        have h := hy (Pi.single i b)
        simpa [trP, Pi.single_apply, ite_mul, Finset.sum_ite_eq', mul_comm] using h
    }
  obtain ⟨m, a, b, c, c₀, hR⟩ := GlobalTheory.T.realMetaplectic_family_derivative_quadratic hP.realMetaplecticRepresentation
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) μ inferInstance _
    hpair A T hAc hadd h0 hA hiso hc1 (hc2 μ inferInstance)
  choose u hu hDu using fun i => GlobalTheory.T.exists_heisenbergLine_derivative_formula M ψ hψ (a i)
  choose v hv hDv using fun i => GlobalTheory.T.exists_heisenbergLine_derivative_formula M ψ hψ (b i)
  obtain ⟨r₀, hr₀, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
  refine ⟨m, u, v, c, c₀, fun i => ⟨hu i, hv i⟩, ?_⟩
  intro f g₁ g₂ h1 h2 F₁ hF y
  have eF : ∀ t, F₁ t = T t f := fun t => hinj _ _ ((hF t r₀ (hr₀ f)).symm.trans (hT t f r₀ (hr₀ f)))
  simp only [eF]
  exact hR f g₁ g₂ (fun i y => hDv i f (g₁ i) (h1 i) y) (fun i y => hDu i (g₁ i) (g₂ i) (h2 i) y) y
end GlobalTheory.OscQuad
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oscillator_lie_action_quadratic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (m : ℕ) (u v : Fin m → Matrix (Fin n) (Fin d) (AE F E)) (c : Fin m → ℂ) (c₀ : ℂ),
      (∀ i, At (evI F) (u i) ∧ At (evI F) (v i)) ∧
      ∀ (f : SInf F (Fin n × Fin d)) (g₁ g₂ : Fin m → SInf F (Fin n × Fin d)),
        (∀ i, ActsD (evI F) (M.heisLine ψ (v i)) f (g₁ i)) → (∀ i, ActsD (evI F) (M.heisLine ψ (u i)) (g₁ i) (g₂ i)) →
        ∀ F₁ : ℝ → SInf F (Fin n × Fin d), (∀ t, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (F₁ t)) →
        ∀ y, HasDerivAt (fun t => F₁ t y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  first | exact @_root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic | exact _root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic | (intros; apply _root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic <;> assumption)
end
