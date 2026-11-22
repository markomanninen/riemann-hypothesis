module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefF
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvarAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSide
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvar
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTer
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A28
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A53

@[expose] public section

namespace PositivityTheory.HtPt.Ktw

theorem a64 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.NefProductNonneg.Statement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.NefProductNonneg.unfolding_matrix_of_form a28 (a63 hR)

theorem a73 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleNefPlusAmple.equiv
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BundleOfDeg.full a65 a71
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDimEq.full).mp (a72 hR)

theorem a77 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionCount.equiv
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.GraphModel.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BundleOfDeg.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDim.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BaseRealises.proof a66
    (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleModel.proof
      PositivityTheory.HtPt.KtwS.SectionsOverLocalization.VeryAmpleEq.full a69) a18).mp
    (GroundTheory.Heights₂.Heights.Kleiman.SectionCount.assembled a39 a43 a48 a51 hR)

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 in
theorem k_twins : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} → NefProductNonneg.Statement ∧ VeryAmpleNefPlusAmple.Statement ∧ SectionCount.Statement :=
  fun hR => ⟨a64 hR, a73 hR, a77 hR⟩

end PositivityTheory.HtPt.Ktw
