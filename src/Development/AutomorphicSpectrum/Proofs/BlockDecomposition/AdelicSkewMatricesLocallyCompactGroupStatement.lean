module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.SiegelWeilFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_skew_matrices_locally_compact_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | exact GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | (intros; apply GlobalTheory.CompanionTheory.SiegelRadTop.nA_top <;> assumption)
