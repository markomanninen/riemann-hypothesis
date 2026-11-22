module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
public import Formalism.PeriodIntegrals.ZuckTensor
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.IsLowUnitH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
public import Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
public import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
public import Formalism.LocalToGlobal.IndefiniteReal.MeasurableMulGA

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

namespace Formalism.L2.SG.EvalTPh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem phLoc_int_of_gap (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (v : NumberField.InfinitePlace X.B.I.F) :
    Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
    (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X Formalism.L2.SG.Closed.CoefWeightedLoc_holds hG) v
  have hs : Integrable (star (Formalism.L2.SG.WuDecayPf.coefV X v)) (Formalism.REAL.muG (X.B.I.ε v)) :=
    memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr h).star
  exact hs.const_mul (X.dv v : ℂ)

variable {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} {E : Submodule ℂ (MMap M)}
  {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {v₀ : M.Vec}

end Formalism.L2.SG.EvalTPh

end
