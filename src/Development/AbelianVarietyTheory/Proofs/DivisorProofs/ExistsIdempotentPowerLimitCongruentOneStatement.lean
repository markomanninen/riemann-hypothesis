module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentPowerLimitCongruentOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedCompleteStatement

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_powerLimit_congruentOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ y ∈ OhE D, y - 1 ∈ hatId D 𝔪 → ∃ g ∈ OhE D, y * g * (y * g) = y * g ∧ y * g - 1 ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.PowIdem.exists_idem | exact GlobalTheory.PowIdem.exists_idem | (intros; apply GlobalTheory.PowIdem.exists_idem <;> assumption)
