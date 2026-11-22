module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCoordsEvaluationLowerRowMapEqTensorBranchinStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LastStepIntegralFormLocalCoordsMemIntegralSpanStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HyperplaneFormIntegralLocalCoordsMemIntegralSpanStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralHyperplaneFormOfLocalCoordsIntegraStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem pendTw_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l))
    (l0 : TC.Law0 I l) (u : B.Word) (a : I.ι), ∃ P : GlobalTheory.PerQ.PendTw (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (TC.tw I l l0 Z) u a, ∀ τ,
      P.br τ = brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u τ) := by
  intro B X I hI l Z l0 u a
  exact ⟨{ br := fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
              (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)
           coM := fun w c => coM I u a w c
           coP := fun w => coP I u a w
           Pt_eq := GlobalTheory.T.localCoords_evaluationLowerRowMap_eq_tensor_branching I hI l Z l0 u a
           lat_co := GlobalTheory.T.lastStepIntegralForm_localCoords_mem_integralSpan I hI l Z l0 u a
           pt_co := fun w z hz => ⟨GlobalTheory.T.hyperplaneFormIntegral_localCoords_mem_integralSpan I hI l Z l0 u a w z hz, GlobalTheory.T.exists_integralHyperplaneForm_of_localCoords_integral I hI l Z l0 u a w z hz⟩ }, fun _ => rfl⟩

end GlobalTheory.PerQ.Co
