module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperatorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLinesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLinesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOneStatement

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : AE F E) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem map_atPl (p : ∀ i, V i →ₗ[ℂ] W i) (w : ι) (L : Module.End ℂ (V w)) (L' : Module.End ℂ (W w))
    (h : p w ∘ₗ L = L' ∘ₗ p w) : PiTensorProduct.map p ∘ₗ atPl w L = atPl w L' ∘ₗ PiTensorProduct.map p := by
  unfold atPl
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp [h]
  · simp [Function.update_of_ne hi]

theorem map_sumPl (p : ∀ i, V i →ₗ[ℂ] W i) (L : ∀ i, Module.End ℂ (V i)) (L' : ∀ i, Module.End ℂ (W i))
    (h : ∀ i, p i ∘ₗ L i = L' i ∘ₗ p i) : PiTensorProduct.map p ∘ₗ sumPl L = sumPl L' ∘ₗ PiTensorProduct.map p := by
  apply LinearMap.ext; intro x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumPl, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (map_atPl p i (L i) (L' i) (h i)) x

end Tensor

theorem i_locfin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := GlobalTheory.T.isLocallyFinite_piTensorSumOfFactorOperators

theorem i_expact : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := GlobalTheory.T.weakExponential_action_on_fockVectors

theorem i_actslaws : GlobalTheory.RealLift.ActsLaws := GlobalTheory.T.archActionReadings_compatible

theorem i_derex : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist

theorem i_fockex : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives

theorem i_vacline : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives

theorem i_polrange : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws

theorem i_genex : GlobalTheory.RealLift.GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist

theorem i_lineex : GlobalTheory.RealLift.LineEx := GlobalTheory.T.unitaryLieElements_generate_oneParamLines

theorem i_kline : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines

theorem i_liescalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine

theorem i_liesecond : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar

theorem i_liefirst : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := GlobalTheory.T.lieFirst_of_lieSecond'

theorem i_frameex : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists

theorem i_parity : GlobalTheory.RealLift.Parity := GlobalTheory.T.realLift_parity

section Helpers

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem atPl_eq (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq, MultilinearMap.map_update_add]

theorem atPl_smul (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq, MultilinearMap.map_update_smul, RingHom.id_apply]

theorem atPl_one (w : ι) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  rw [atPl_eq, show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by
    funext i; by_cases h : i = w
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]]
  exact PiTensorProduct.map_id

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq, MultilinearMap.map_update_zero]

end Helpers

section Exp

variable {V V' Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Z] [Module ℂ Z]

theorem pow_comm {q : V →ₗ[ℂ] Z} {L : Module.End ℂ V} {L0 : Module.End ℂ Z} (h : q ∘ₗ L = L0 ∘ₗ q) (n : ℕ) (v : V) :
    q ((L ^ n) v) = (L0 ^ n) (q v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, ← LinearMap.comp_apply, h,
      LinearMap.comp_apply]

theorem exp_equiv {q : V →ₗ[ℂ] Z} {q' : V' →ₗ[ℂ] Z} {L U : Module.End ℂ V} {L' U' : Module.End ℂ V'} {L0 : Module.End ℂ Z}
    (hU : IsExp L U) (hU' : IsExp L' U') (h : q ∘ₗ L = L0 ∘ₗ q) (h' : q' ∘ₗ L' = L0 ∘ₗ q') {v : V} {v' : V'}
    (e : q v = q' v') : q (U v) = q' (U' v') := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (q (U v) - q' (U' v'))).1 fun l => ?_)
  rw [map_sub, sub_eq_zero]
  have a := hU v (l ∘ₗ q)
  have b := hU' v' (l ∘ₗ q')
  simp only [LinearMap.comp_apply, pow_comm h, pow_comm h', e] at a b
  exact a.unique b

end Exp

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Side

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

include Φ in
theorem pol_eq (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ T, f = Φ T := by
  rw [← hrange] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨T, rfl⟩

end Side

section SideW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

end SideW

theorem zero_mem_upq (R S : ℕ) : (0 : Mat R S) ∈ upq R S := by simp [upq]

end GlobalTheory.RealLift.Main
