module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGeneratoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAddCharSymplecticSelfPairingPlaceCoordStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOneStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacAny

private theorem supported_sum {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {ι : Type} (s : Finset ι) {f : ι → AF F}
    (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
  intro u hu
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi u hu

private theorem supported_neg {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x : AF F}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (-x) := by
  intro u hu
  rw [smul_neg, h u hu, neg_zero]

private theorem supported_atPlace {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (t : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (GlobalTheory.EmbChart.atPlace v t) := by
  intro u hu
  rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]

private theorem supported_mul_right {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x : AF F}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) (y : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := by
  intro u hu
  rw [smul_eq_mul, ← mul_assoc, show u * x = 0 from hx u hu, zero_mul]

private theorem supported_mul_left {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (x : AF F) {y : AF F}
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := by
  rw [mul_comm]
  exact supported_mul_right hy x

private theorem supported_sub {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x y : AF F}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x)
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x - y) := by
  intro u hu
  rw [smul_sub, hx u hu, hy u hu, sub_self]

private theorem evFin_invOf_two_local {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} :
    GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
  refine (invOf_eq_right_inv ?_).symm
  have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by
    rw [mul_invOf_self, map_one]
  rwa [map_mul, map_ofNat] at h

theorem exists_isVac_any_darboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ φ, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v φ := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co v
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  obtain ⟨M, _, g, hΓ⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_integral_span_generators X Y hX.lat.toIsLattice hY.lat.toIsLattice v
  let γf : (M → v.adicCompletionIntegers F) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    fun a => ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)
  let u : M → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun m =>
    (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i),
     fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i))
  let χ : (M → v.adicCompletionIntegers F) → ℂ := fun a => B.ψ (⅟(2 : AF F) *
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γf a) (γf a))
  have he : ∀ a, co.e (γf a) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [γf, map_sum, map_smul]
  have hcomp : ∀ a i, (co.e (γf a)).1 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i ∧
      (co.e (γf a)).2 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i := by
    intro a i
    rw [he]
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, smul_eq_mul]
  have hAt : ∀ a i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 i) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).2 i) := by
    intro a i
    rw [(hcomp a i).1, (hcomp a i).2]
    exact ⟨supported_sum _ fun m _ => supported_mul_right (supported_atPlace _) _,
      supported_sum _ fun m _ => supported_mul_right (supported_atPlace _) _⟩
  have hev : ∀ a, ((fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i)),
      (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i))) = ∑ m, (a m : Fv F v) • u m := by
    intro a
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [(hcomp a i).1, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Finset.sum_apply, u]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [(hcomp a i).2, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.snd_sum, Finset.sum_apply, u]
  have hψ : ∀ z : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      B.ψ z = GlobalTheory.VacAny.psiV B.ψ v (GlobalTheory.AdelicU.evFin F v z) := fun z hz => by
    rw [GlobalTheory.VacAny.psiV_apply, ← GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v z hz]
  have hzero : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → γf a = 0 := by
    intro a h
    rw [← hev a] at h
    have h1 : co.e (γf a) = 0 := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · rw [GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v _ (hAt a i).1, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i) = 0 from
          congrFun (congrArg Prod.fst h) i, map_zero]
        rfl
      · rw [GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v _ (hAt a i).2, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i) = 0 from
          congrFun (congrArg Prod.snd h) i, map_zero]
        rfl
    exact co.e.map_eq_zero_iff.1 h1
  have hker : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1 := by
    intro a h
    simp only [χ, hzero a h]
    simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
  have hadd : ∀ a b, γf (a + b) = γf a + γf b := by
    intro a b
    simp only [γf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (((a + b) m : v.adicCompletionIntegers F) : Fv F v) = (a m : Fv F v) + b m from rfl, map_add (f := _), add_smul]
  have hmem : ∀ a, γf a ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := fun a => (hΓ _).2 ⟨a, rfl⟩
  have hdot : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) ∧
      GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) =
        (∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 := by
    intro a b
    refine ⟨supported_sum _ fun i _ => supported_mul_right (hAt a i).1 _, ?_⟩
    rw [← hev a, ← hev b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
  have hcoc : ∀ a b, χ (a + b) = χ a * χ b * GlobalTheory.VacAny.psiV B.ψ v
      (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
        (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2))) := by
    intro a b
    simp only [χ]
    rw [hadd, GlobalTheory.T.addChar_halfTrace_tensorLattice_heisenbergCocycle B hB X Y r s r' s' hX hY θ hθ v _ (hmem a) _ (hmem b), co.form]
    congr 1
    have hz := supported_neg (supported_mul_left (⅟(2 : AF F))
      (supported_sub (hdot a b).1 (hdot b a).1))
    rw [hψ _ hz, map_neg, map_mul, map_sub, (hdot a b).2, (hdot b a).2, evFin_invOf_two_local]
  obtain ⟨φ, hφSB, hφ0, hφ⟩ := GlobalTheory.T.exists_schroedinger_eigenvector_compact_cocycle v (GlobalTheory.VacAny.psiV B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (GlobalTheory.T.standardTraceAdelicAddChar_localComponent_ne_one B.ψ hB.std v) u χ (GlobalTheory.T.continuous_addChar_symplecticSelfPairing_placeCoordinates σ B.ψ hB.std.1 X.J Y.J (θ : E) v g) hker hcoc
  refine ⟨φ, hφSB, hφ0, θ, hθ, ?_⟩
  intro γ hγ
  obtain ⟨a, rfl⟩ := (hΓ γ).1 hγ
  intro rr hrr
  show GlobalTheory.WeilM.schr B.ψ (co.e (γf a)) _ = _
  rw [GlobalTheory.T.adelicSchrodinger_tensor_eq_local_of_supportedAt B.ψ v (co.e (γf a)) (fun i => (hAt a i).1) (fun i => (hAt a i).2) φ rr hrr.1, hev a, hφ a]

end GlobalTheory.VacAny
