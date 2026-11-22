module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistTilde
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeShift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFiniteE
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSubquotFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotFiltX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotIsoX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubFamilyTwistX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotDevissage
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PMulQuotEq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionNonvanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionMulInj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

namespace SnapperSectionClosed

theorem snapperFinite : SnapperFinite.Statement.{u, w, w} :=
  SnapperFinite.proof Extension.full Extension.full TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

theorem quotAdd : SnapperQuotAdd.Statement.{u, w, w} :=
  SnapperQuotAdd.proof (SnapperSubquotFinite.proof snapperFinite)

theorem quotDevissage : SnapperQuotDevissage.Statement.{u, w, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof quotAdd SubFamilyTwist.proof

end SnapperSectionClosed


open SnapperSectionClosed in
theorem SnapperSection.full : SnapperSection.Statement.{u, w} :=
  SnapperSection.proof quotAdd quotDevissage MulQuotEq.proof SectionNonvanish.proof SectionMulInj.proof

end GroundTheory.Heights₂.Heights.Kleiman
