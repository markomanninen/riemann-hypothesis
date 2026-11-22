module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDSq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDegLocExact
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTop
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechFlat
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechCone
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTransport
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurent
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurentCohom
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePoly
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFree
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedPres
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedULift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCohomRetract
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreVanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreOnto
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenerated
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSections
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PProjDegreePositive
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleCover
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGeneratedAmple
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnW
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThree
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestriction
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepDataJProper
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDrop
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCount

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem CechDSq.full : CechDSq.Statement.{u, v} := CechDSq.proof
theorem DegLocExact.full : DegLocExact.Statement.{u, v} := DegLocExact.proof
theorem CechExact.full : CechExact.Statement.{u, v} := CechExact.proof CechDSq.full DegLocExact.full
theorem CechTop.full : CechTop.Statement.{u, v} := CechTop.proof
theorem Cech.Cone.full : Cech.Cone.Statement.{u, v} := Cech.Cone.proof
theorem Cech.Transport.full : Cech.Transport.Statement.{u, v, w} := Cech.Transport.proof
theorem SerrePoly.Laurent.full : SerrePoly.Laurent.Statement.{u} := SerrePoly.Laurent.proof
theorem SerrePoly.LaurentCohom.full : SerrePoly.LaurentCohom.Statement.{u} :=
  SerrePoly.LaurentCohom.proof Cech.Cone.full
theorem SerrePoly.full : SerrePoly.Statement.{u} :=
  SerrePoly.proof SerrePoly.Laurent.full Cech.Transport.full SerrePoly.LaurentCohom.full
theorem SerreFree.full : SerreFree.Statement.{u, v} := SerreFree.proof SerrePoly.full
theorem GradedPres.full : GradedPres.Statement.{u, v} := GradedPres.proof
theorem GradedULift.full : GradedULift.Statement.{u, v} := GradedULift.proof
theorem CohomRetract.full : CohomRetract.Statement.{u, v, w} := CohomRetract.proof

theorem SerreFinite.full : SerreFinite.Statement.{u, v} :=
  SerreFinite.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreVanish.full : SerreVanish.Statement.{u, v} :=
  SerreVanish.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreOnto.full : SerreOnto.Statement.{u, v} :=
  SerreOnto.proof CechExact.full SerreFree.full SerreVanish.full

theorem SerreTail.full : SerreTail.Statement.{u, v} := SerreTail.proof SerreFinite.full SerreOnto.full

theorem Extension.full : Extension.Statement.{u, v, w} := Extension.proof
theorem Generated.full : Generated.Statement.{u, w} := Generated.proof Extension.full
theorem TwistFinite.full : TwistFinite.Statement.{u, w} := TwistFinite.proof Extension.full SerreFinite.full
theorem TwistSections.full : TwistSections.Statement.{u, w} := TwistSections.proof SerreOnto.full
theorem ProjDegreePositive.full : ProjDegreePositive.Statement.{u} := ProjDegreePositive.proof
theorem HilbertPositive.full : HilbertPositive.Statement.{u, w} :=
  HilbertPositive.proof ProjDegreePositive.full TwistSections.full
theorem PrimeFiltration.Point.full : PrimeFiltration.Point.Statement.{u, w} := PrimeFiltration.Point.proof
theorem PrimeFiltration.Restrict.full : PrimeFiltration.Restrict.Statement.{u, w} :=
  PrimeFiltration.Restrict.proof

theorem StepThree.Away.full : StepThree.Away.Statement.{u, w} := StepThree.Away.proof
theorem RestrictTwist.full : RestrictTwist.Statement.{u, w} := RestrictTwist.proof
theorem StepData.JProper.full : StepData.JProper.Statement.{u, w} := StepData.JProper.proof
theorem SubvarDrop.full : SubvarDrop.Statement.{u, w} := SubvarDrop.proof

theorem TwistVanish.assembled (hS : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} :=
  TwistVanish.proof Extension.full SerreVanish.full hS

theorem NefRestrict.assembled (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} :=
  NefRestrict.proof RestrictTwist.full hRL

theorem SectionCount.Drop.assembled (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} :=
  SectionCount.Drop.proof hF hT hH hR

theorem SectionCount.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w}) :
    SectionCount.Statement.{u, w} :=
  SectionCount.proof hTop (SectionCount.Drop.assembled hF hT hH hR)

theorem StepThree.assembled (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.Statement.{u, w} :=
  StepThree.proof StepThree.Away.full (StepThree.OnW.proof hL hG)

end GroundTheory.Heights₂.Heights.Kleiman
