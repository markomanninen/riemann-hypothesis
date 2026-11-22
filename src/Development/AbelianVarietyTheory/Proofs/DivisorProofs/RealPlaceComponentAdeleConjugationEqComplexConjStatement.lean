module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piInf τ (cA σ z) = star (piInf τ z) := by
  first | exact @GlobalTheory.RealPlaceConj.piInf_cA_eq_star | exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star | (intros; apply GlobalTheory.RealPlaceConj.piInf_cA_eq_star <;> assumption)
