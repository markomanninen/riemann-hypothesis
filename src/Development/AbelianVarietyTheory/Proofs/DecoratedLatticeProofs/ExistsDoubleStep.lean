module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open GlobalTheory.LocMod Filter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.DblInhab

section Gram

variable (E : Type) [Field E] [CharZero E] [StarRing E]



end Gram


section Place

open GlobalTheory.FinPl (SplitPt Pl idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := GlobalTheory.LocChar.ι_one (ofSplit q)

theorem sec_mul_pr (a : k) (o : AE D) : q.sec (a * q.pr o) = q.sec a * o := by
  have h := q.sec_pr (q.sec a * o)
  rw [map_mul, q.pr_sec] at h
  rw [h, ← mul_assoc]
  exact congrArg (· * o) (GlobalTheory.LocChar.e_mul_ι (ofSplit q) a)

theorem sec_mem_idAt (a : k) : q.sec a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  obtain ⟨hee, hec, -⟩ := q.split
  have he : q.e ∈ idAt D (· = q.v) := by
    refine ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 q.e).2 ?_
    rw [← hsum, add_mul, hee, mul_comm (cA D q.e), hec, add_zero]
  have h : q.e * q.sec a = q.sec a := GlobalTheory.LocChar.e_mul_ι (ofSplit q) a
  rw [← h]
  exact Ideal.mul_mem_right _ _ he

theorem sec_mem_intAt (a : k) : q.sec a ∈ intAt D (· = q.v) ↔ valuation k a ≤ 1 :=
  (and_iff_right (sec_mem_idAt q a)).trans (q.int_iff a).symm

theorem pr_le_one {o : AE D} (ho : o ∈ intAt D (· = q.v)) : valuation k (q.pr o) ≤ 1 := by
  refine (q.int_iff _).2 ?_
  rw [q.sec_pr, ← sec_one, map_mul]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ((q.int_iff 1).1 (one_mem _)) ho.2

end Place


end GlobalTheory.LocMod.DblInhab

end
