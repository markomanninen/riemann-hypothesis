module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XMemMIdealOverIff
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Assembly
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqSegreRealise
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubalgebraOfInvMem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSide
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLast
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfModelNumEq

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.Kleiman

theorem KleimanNefB.segreRealise (hNef : SectionsOverLocalization.NefEq.Statement) (hCh : SectionsOverLocalization.ModelChangeNef.Statement)
    (hNM : SectionsOverLocalization.NumModel.Statement) : SectionsOverLocalization.SegreRealise.Statement :=
  SectionsOverLocalization.SegreRealise.proof SectionsOverLocalization.SegreBase.proof SectionsOverLocalization.SegreTwist.proof SectionsOverLocalization.SegreDim.proof
    (SectionsOverLocalization.SegreNef.proof SectionsOverLocalization.SegreDim.proof SectionsOverLocalization.SegreNum.proof) SectionsOverLocalization.SegreNum.proof
    SectionsOverLocalization.BundleOfDeg.full SectionsOverLocalization.ModelDimEq.full (SectionsOverLocalization.ModelNefEq.proof hNef hCh)
    (SectionsOverLocalization.ModelNumEq.proof hNM)

end GroundTheory.Heights₂.Heights.ForSecondHalf
