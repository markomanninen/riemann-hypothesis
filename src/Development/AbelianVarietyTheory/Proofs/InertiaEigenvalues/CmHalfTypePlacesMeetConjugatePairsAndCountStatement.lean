module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCount
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitCount in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  intro D i hl s
  have hx : ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
    intro w hw w' h
    have hw' := mem_placesOver_of_conj D.host hw h
    have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
    have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
    rcases GlobalTheory.T.splitPrime_place_cmType_conjugate D i hl w w' hw hw' h with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩
  have := D.host.hostE_isGalois
  obtain ⟨hfin, hdeg⟩ := locDeg_mul_ncard D.host.E hl.1
  let C := columns (N := D.nd) D.nbr i s
  have hsub : C ⊆ placesOver D.host.E (D.nd.l i) := fun _ ⟨hw, _⟩ => hw
  have hCf : C.Finite := hfin.subset hsub
  refine ⟨hx, hCf, fun w hw => ?_⟩
  have hinj : Function.Injective (cPl D.host) := Function.LeftInverse.injective (cPl_cPl D.host)
  have hun : placesOver D.host.E (D.nd.l i) = C ∪ cPl D.host '' C := by
    ext v
    constructor
    · intro hv
      rcases hx v hv _ (isConjPl_cPl D.host v) with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨_, h.1, cPl_cPl D.host v⟩
    · rintro (hv | ⟨u, hu, rfl⟩)
      · exact hsub hv
      · exact mem_placesOver_of_conj D.host (hsub hu) (isConjPl_cPl D.host u)
  have hdis : Disjoint C (cPl D.host '' C) := by
    rw [Set.disjoint_left]
    rintro _ hv ⟨u, hu, rfl⟩
    rcases hx u (hsub hu) _ (isConjPl_cPl D.host u) with h | h
    · exact h.2 hv
    · exact h.2 hu
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h := hdeg w hw
  rw [hun, Set.ncard_union_eq hdis hCf (hCf.image _), Set.ncard_image_of_injective _ hinj, hfr] at h
  rw [Nat.mul_add] at h
  change locDeg D.host.E w * C.ncard = D.R.f
  omega
