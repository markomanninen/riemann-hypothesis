module

public import Development.EtaleCohomology.CohomologicalPurity.OffContBasicPfR
public import Development.EtaleCohomology.CohomologicalPurity.ResLECompIsoOpenInfPreimageHomNaturality
public import Development.EtaleCohomology.CohomologicalPurity.OffContLocKnxPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHsContPfFive
public import Development.EtaleCohomology.CohomologicalPurity.LeafNbhdExcPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokInjPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafSurjGeoPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafInjGeoPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf
public import Development.EtaleCohomology.CohomologicalPurity.PresSheafify
public import Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf
public import Development.EtaleCohomology.CohomologicalPurity.FreePMapMk
public import Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafImgPf

@[expose] public section

namespace LateralTheory.Fix.LeafIndExc
open LateralTheory.CohomologicalPurity

theorem bd : LeafBd :=
  Bd.goal_of Bd.LeafMono_of Bd.LeafPush_of Bd.LeafGood_of Bd.LeafDelta_of Bd.LeafExact_of
    (Bd.LeafImg_of (Bd.LeafImgHom_of Bd.LeafGen_of))

theorem exc : LeafExc :=
  LeafExc_of (LeafExcFormal_of EtaleExcIdent LeafExcDeg_of)
    (LeafExcSheaf_of (LeafFreeCok_of_inj LeafFreeCokInj_of) LeafSurjGeo_of LeafInjGeo_of)

theorem offCont : LeafOffCont :=
  leafOffCont_of offContBasic_of (etale_purity_continuity_off_closed_of_local_and_chase OffContLoc_of OffChaseGeo_full)

theorem intersectionNumber_baseChange : LeafIndExc :=
  leafIndExc_of (leafNbhdExc_of exc) (leafHsCont_of' bd exc offCont)

end LateralTheory.Fix.LeafIndExc
