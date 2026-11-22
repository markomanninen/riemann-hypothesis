module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), GlobalTheory.Doubling.IsMaj V a → ∀ w, Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) ∧ ∀ g, 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ≤ 1 := by
  first | exact @GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one | exact GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one | (intros; apply GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one <;> assumption)
