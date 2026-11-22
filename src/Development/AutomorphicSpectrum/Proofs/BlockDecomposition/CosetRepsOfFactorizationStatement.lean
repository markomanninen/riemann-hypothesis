module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetRepsOfFactorization
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_reps_of_factorization : ∀ (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop), P 1 → Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I) → (∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) → ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧ ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | exact GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | (intros; apply GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property <;> assumption)
