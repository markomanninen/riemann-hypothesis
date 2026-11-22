module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMixedTwistShift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplane
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotDevissageX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplaneMid
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperSectionX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDiffPoly
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrLenEuler
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubsetDiffConst
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumEventual
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterSumTopVanish
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumAdditive

@[expose] public section

namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem snapperHyperplane : SnapperHyperplane.Statement.{u, w} :=
  SnapperHyperplane.proof SnapperQuotAdd.closed SnapperQuotDevissage.closed SnapperHyperplaneMid.proof

theorem mixedTwistShift : MixedTwistShift.Statement.{u, w} :=
  MixedTwistShift.proof snapperHyperplane SnapperSection.full SnapperDiffPoly.proof RestrLenEuler.proof
    SubsetDiffConst.proof

theorem interNumEventual : InterNumEventual.Statement.{u, w} :=
  InterNumEventual.proof snapperHyperplane SnapperSection.full

theorem interNumAdditive : InterNumAdditive.Statement.{u, w} :=
  InterNumAdditive.proof interNumEventual (InterSumTopVanish.proof mixedTwistShift)

end PositivityTheory.HtPt.Kra
