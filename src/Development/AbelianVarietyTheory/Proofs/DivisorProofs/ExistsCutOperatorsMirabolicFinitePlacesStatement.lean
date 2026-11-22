module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCutOperatorsMirabolicFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cutOperators_mirabolic_finitePlaces : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  first
  | exact @GlobalTheory.JSW.MirPatch.cut_operators
  | exact GlobalTheory.JSW.MirPatch.cut_operators
  | (intros; apply GlobalTheory.JSW.MirPatch.cut_operators <;> assumption)
