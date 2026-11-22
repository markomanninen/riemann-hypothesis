module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCutOperator_transfer_adelicWhittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  first | (exact @GlobalTheory.JSW.CutTransfer.transfer) | (exact GlobalTheory.JSW.CutTransfer.transfer) | (intros; apply GlobalTheory.JSW.CutTransfer.transfer  <;> assumption)
