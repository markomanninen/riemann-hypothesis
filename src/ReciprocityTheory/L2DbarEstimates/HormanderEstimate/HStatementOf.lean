module

public import ReciprocityTheory.L2DbarEstimates.Localization.SSmooth
public import ReciprocityTheory.L2DbarEstimates.Localization.MultAdj
public import ReciprocityTheory.L2DbarEstimates.Localization.Cutoff
public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightRel
public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBack
public import ReciprocityTheory.L2DbarEstimates.Localization.Localize
public import ReciprocityTheory.L2DbarEstimates.Localization.Extend
public import ReciprocityTheory.L2DbarEstimates.Localization.IntegrableFd
public import ReciprocityTheory.L2DbarEstimates.Localization.ChartFlat
public import ReciprocityTheory.L2DbarEstimates.Localization.Imports
public import ReciprocityTheory.L2DbarEstimates.Localization.PrimZeroOfNonpos
public import ReciprocityTheory.L2DbarEstimates.Localization.DerivSmoothTransitionOfOneLt
public import ReciprocityTheory.L2DbarEstimates.Localization.ShellCeilEq
public import ReciprocityTheory.L2DbarEstimates.Localization.LeviZCoordChart
public import ReciprocityTheory.L2DbarEstimates.Localization.Choice
public import ReciprocityTheory.L2DbarEstimates.Localization.Primed
public import ReciprocityTheory.L2DbarEstimates.Localization.Closure
public import ReciprocityTheory.L2DbarEstimates.Localization.KPsiHasCompactSupport
public import ReciprocityTheory.L2DbarEstimates.Localization.SplitTest
public import ReciprocityTheory.L2DbarEstimates.Localization.Locality
public import ReciprocityTheory.L2DbarEstimates.Localization.TestIneq
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.RegMDbEqZeroOfNotMem
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Hormander

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.F

theorem hStatement_of (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (hAP : APStatement n M) (hTIbp : TStarIbpStatement n M) (hChain : ChainStatement n M)
    (hReg : C.RegStatement) (hGraph : B.GraphSt (V n) MeasureTheory.volume ℝ)
    (hSmooth : B.SmoothSt (V n) MeasureTheory.volume) (hSupp : B.SupportSt (V n) MeasureTheory.volume)
    (hStd : B.StdSt (V n) MeasureTheory.volume) : HStatement n M :=
  hormander n M
    (testIneq n M
      (choice n M chi (psi n M) (shell n M) (leviNormSq n M) hChain)
      (primedIneq n M hAP)
      (closureIneq n M
        (dens n M (cutoff n M (multAdj n M) (multS n M)) (unweightRel n M) (unweightBack n M)
          (localize n M (multDiv n M) (multS n M))
          (chartFlat n M (extend n M) (flatGraph n hGraph hSmooth hSupp hStd))))
      (splitTest n M (kSub n M) (weakSSmooth n M) (sbarDbar n M) hTIbp)
      (locality n M) (weakSSmooth n M) (sbarDbar n M))
    (regM n M hReg (extend n M))

end ReciprocityTheory.L2DbarEstimates.F
