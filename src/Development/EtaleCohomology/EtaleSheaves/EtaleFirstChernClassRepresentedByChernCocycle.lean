module

public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.EtaleCohomology.EtaleSheaves.TwPairExists
public import Development.EtaleCohomology.EtaleSheaves.LeafNatCupPf
public import Development.EtaleCohomology.EtaleSheaves.LeafNatOnePf
public import Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality
public import Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf
public import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
public import Development.EtaleCohomology.EtaleSheaves.UnitSections
public import Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
public import Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
public import Development.EtaleCohomology.EtaleSheaves.ChernClassEvaluation
public import Development.EtaleCohomology.EtaleSheaves.LeafEvMkPf
public import Development.EtaleCohomology.EtaleSheaves.ChernClassValueFirst
public import Development.EtaleCohomology.EtaleSheaves.ChernClassValueSecond
public import Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleFirst
public import Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleSecond
public import Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleThird
public import Development.EtaleCohomology.EtaleSheaves.LeafRootLocPf
public import Development.EtaleCohomology.TateTwists.EtaleKummerTorsorRootsOfUnityListTorsionExistsOf
public import Development.EtaleCohomology.TateTwists.HoldsOf

@[expose] public section

namespace LateralTheory.E.LeafA6nat_xy7V2Cut

theorem kumTExists : LateralTheory.E.CupProductRingLaws.LeafKumTExists := fun q _ =>
  ⟨_, LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange q⟩

theorem oneSpec : LateralTheory.E.CupProductRingLaws.LeafOneSpec :=
  LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of
    (LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit LateralTheory.E.UnitSections.LeafUnitSec_of)
    LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of

theorem etaleFirstChernClass_represented_by_chern_cocycle : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle :=
  have hr := LateralTheory.E.LeafRootLocPf.LeafRootLoc_of
  LateralTheory.E.ChernClassRootLocalization.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique
    (LateralTheory.E.ChernClassEvaluation.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness LateralTheory.E.LeafEvMkPf.LeafEvMk_of
      (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor hr kumTExists) (LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor.etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor hr kumTExists)
      (LateralTheory.E.ChernCocycleEdgeCoboundary.etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots hr) (LateralTheory.E.ChernCocycleFaceFormulas.etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r hr) (LateralTheory.E.ChernCocycleFaceDegeneracyIdentities.etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization hr))
    hr

theorem natKum : LateralTheory.E.CupProductRingLaws.LeafNatKum := fun q _ =>
  ((LateralTheory.Fix.EtaleKummerClassExplicitCocycle.holds_of LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange) q).2.1

theorem goal_of : LateralTheory.E.D2.LeafA6nat := fun q _ =>
  ⟨LateralTheory.E.LeafNatCupPf.LeafNatCup_of LateralTheory.Fix.CupProductTensor.cupSpec q,
   LateralTheory.E.LeafNatOnePf.LeafNatOne_of oneSpec q,
   LateralTheory.E.FirstChernNaturality.etale_first_chern_class_natural_of_spec etaleFirstChernClass_represented_by_chern_cocycle q,
   natKum q⟩

end LateralTheory.E.LeafA6nat_xy7V2Cut
