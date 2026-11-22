module

public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.ResMapNsmulHomotopy
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuPf
public import Development.EtaleCohomology.EtaleSheaves.KummerFields.H0Naturality
public import Development.EtaleCohomology.EtaleSheaves.KummerFields.GmSecSurj
public import Development.EtaleCohomology.EtaleSheaves.LeafKumCut

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKumFieldPf

open LateralTheory.E.E4

theorem kumMu : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumMu := fun hy =>
  LateralTheory.E.H2CurveOrder.LeafKumMuPf.LeafKumMu_of hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2.2.1
    LateralTheory.E.H2CurveOrder.muUnits hy

theorem etale_kummer_sequence_degree_zero_global_sections : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.KummerUnitsSurjectH0 := fun hy =>
  LateralTheory.E.H2CurveOrder.KummerH0Surjection.etale_kummer_degree_zero_cohomology_of_sections_and_units_surjective LateralTheory.E.H2CurveOrder.kumSecSurj
    (LateralTheory.E.LeafKumFieldPf.H0Naturality.etale_degree_zero_cohomology_natural_in_sheaf hy.2.2.2.2.2.2.2.1)
    LateralTheory.E.LeafKumFieldPf.GmSecSurj.LeafGmSecSurj_of hy

theorem kumSeq : LateralTheory.E.LeafKumCut.LeafKumSeq :=
  LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumSeq_of kumMu etale_kummer_sequence_degree_zero_global_sections

end LateralTheory.E.LeafKumFieldPf
