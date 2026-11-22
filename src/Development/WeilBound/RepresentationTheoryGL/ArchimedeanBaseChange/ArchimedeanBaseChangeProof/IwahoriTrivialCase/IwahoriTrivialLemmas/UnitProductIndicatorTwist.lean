module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedArtinianInvolutionIdempotentSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinMatrixReducedOfCharpolySeparable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPreimageQuadraticMapNoNullVectors

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem PositivityTheory.BcbA.Ties.unit_product_indicator_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Separable → Q₂.Separable → stTw2 a b w Q₁ Q₂ ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) : Set _).indicator 1) = stTw a w Q₁ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) * stTw b w Q₂ ((GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)).indicator 1) :=
  GlobalTheory.BCT.UnitProd.stTw2_unit
