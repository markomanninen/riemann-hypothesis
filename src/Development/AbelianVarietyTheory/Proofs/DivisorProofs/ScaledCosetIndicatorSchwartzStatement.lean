module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_coset_indicator_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  exact @GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB
