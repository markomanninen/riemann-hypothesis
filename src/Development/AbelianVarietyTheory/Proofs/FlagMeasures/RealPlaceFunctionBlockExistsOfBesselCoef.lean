module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFromLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapBigOfComparison
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WlocExistsReal

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.WBlockExists

theorem nUnimodLoc : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  intro k r ε e f wf z0 z c hF hc hz
  exact n_unimodular_local k r ε e f wf z0 z c
    ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem realPlaceFunctionBlockExists_of_bessel_coef : BesselNVGap → CoefWeightedLoc → ∀ D : D7, GlobalTheory.St.WBlkExists D :=
  by
    intro hB hCW D hG A L Ps Rf Bu Pi Mu
    obtain ⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ := A
    exact Formalism.L2.SG.Pf.WFL.wblk_core quotient_product_compact
      Formalism.L2.SG.Pf.WFL.locHNProps_holds nUnimodLoc
      Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply hB hCW
      GlobalTheory.wlocExists_real (GlobalTheory.GapAtRealPlaces.gapBigOfGapHyp D)
      hG I ιE ιE_conj ιE_F bas J_eq L_eq pl φ_eq n_eq eps_eq L Ps Rf Bu Pi Mu

end GlobalTheory.WBlockExists
