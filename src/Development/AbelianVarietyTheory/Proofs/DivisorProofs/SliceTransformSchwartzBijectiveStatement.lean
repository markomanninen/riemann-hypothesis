module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_transform_schwartz_bijective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  first | exact @GlobalTheory.SwapSliceBij.sliceT_bijOn | exact GlobalTheory.SwapSliceBij.sliceT_bijOn | (intros; apply GlobalTheory.SwapSliceBij.sliceT_bijOn <;> assumption)
