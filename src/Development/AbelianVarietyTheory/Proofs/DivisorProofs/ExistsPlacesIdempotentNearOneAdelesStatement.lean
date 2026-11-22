module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlacesIdempotentNearOneAdeles
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_placesIdempotent_near_one_adeles : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) → ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  first | exact @GlobalTheory.placesIdem_tendsto_one | exact GlobalTheory.placesIdem_tendsto_one | (intros; apply GlobalTheory.placesIdem_tendsto_one <;> assumption)
