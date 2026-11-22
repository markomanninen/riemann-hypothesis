module

public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohField
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohMu
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTate
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTateA

@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem top_tate : Formalism.GaloisCohomology.LocalTateDualityK := tate_of gcRep gc0 gc1 gc2 gcField gcMu

end PositivityTheory.LocalTateOrthogonality.Gcoh
