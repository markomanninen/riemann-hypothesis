module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataUnitShiftRelation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkCommOfLaws

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_data_unit_shift_relation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ) → _root_.GlobalTheory.MiTop.LinkCommutes f := by
  first | exact @_root_.GlobalTheory.MiTop.linkComm_of_laws_alt | exact _root_.GlobalTheory.MiTop.linkComm_of_laws_alt | (intros; apply _root_.GlobalTheory.MiTop.linkComm_of_laws_alt <;> assumption)
end
