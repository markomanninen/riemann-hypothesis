module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AntidiagonalUnipotentConjSiegelSquareSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antidiagonalUnipotent_conj_siegel_square_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  first | exact @GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left | exact GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left | (intros; apply GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left <;> assumption)
