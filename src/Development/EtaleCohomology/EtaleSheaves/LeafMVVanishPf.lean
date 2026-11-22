module

public import Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPf
public import Development.EtaleCohomology.EtaleSheaves.MVSpcPf
public import Development.EtaleCohomology.EtaleSheaves.PullInjOfIso
public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf
public import Development.EtaleCohomology.TateTwists.EtaleSheafSectionLocallyIffOfPresheafFacts
public import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosureProperties
public import Development.EtaleCohomology.TateTwists.EtaleFreeSheafHomUniversalPropertyHolds
public import Development.EtaleCohomology.TateTwists.EtaleMayerVietorisShortExactSequenceFreeOfCompon

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafMVVanishPf

theorem mvSpc : LateralTheory.E.MVPf.MVSpc :=
  LateralTheory.E.MVPf.MVSpc_of (fun R _ _ _ _ f g h => LateralTheory.Fin.EtaleMayerVietorisChainsShortExact.intersectionNumber_baseChange R f g h)

end LateralTheory.E.LeafMVVanishPf

namespace LateralTheory.E.E8
open LateralTheory.E.LeafMVVanishPf

end LateralTheory.E.E8
