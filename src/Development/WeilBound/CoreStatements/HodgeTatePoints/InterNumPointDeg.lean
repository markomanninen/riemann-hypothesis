module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFilt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFiltStep
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PCutRestrLenExact
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumCut
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumPointDeg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX

@[expose] public section

namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem surjectiveClosed : SurjectiveClosed.Statement.{u, w} :=
  SurjectiveClosed.proof Extension.proof IdealTwistFamily.proof (TildeVanish.proof SerreVanish.full)

theorem finiteSections : FiniteSections.Statement.{u, w} :=
  FiniteSections.proof Extension.proof (TildeTail.proof SerreTail.full)

theorem intersectionNumberCut_of_mixedTwistShift (h : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  InterNumCut.proof (CycleSplit.Filt.proof (CycleSplit.Filt.Step.proof surjectiveClosed finiteSections))
    (CutRestrLenExact.proof surjectiveClosed finiteSections) h

theorem interNumPointDeg : InterNumPointDeg.Statement.{u, w} :=
  InterNumPointDeg.proof (InterNumRestrict.proof
    (RestrLenRestrict.proof surjectiveClosed PrimeFiltration.RestrictQuot.proof))

end PositivityTheory.HtPt.Kra
