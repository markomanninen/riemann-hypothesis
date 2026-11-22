module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiActions_match_through_linkMap : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D σ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (W W₀ : HSp D) (d : HypDec W W₀ ρ), ∀ n ∈ flagN d, l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d B.L (yZero B.L ρ B.ζ) n ∧ cenT d B.L (yZero B.L ρ B.ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  first | exact @GlobalTheory.Unf.LinkPoint.link_point | exact GlobalTheory.Unf.LinkPoint.link_point | (intros; apply GlobalTheory.Unf.LinkPoint.link_point <;> assumption)
