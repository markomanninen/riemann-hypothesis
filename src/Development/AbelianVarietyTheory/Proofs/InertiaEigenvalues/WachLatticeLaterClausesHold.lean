module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LettersFree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeComparisonDcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemH1fIffResMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPointsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleSaturatedExactnessCrystallineStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystallineStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleDescentToTameSubextensionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernelStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHoldsStatement

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL

theorem wach_used_clauses (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : DeltaInvariantNormBound D HW F Cm := by
  unfold DeltaInvariantNormBound
  refine ⟨GlobalTheory.NL.LetterFree.letters_free D HW F, GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm,
    GlobalTheory.NL.CmpCris.wachLattice_comparison_dcris D HW F Cm, GlobalTheory.T.wach_lattice_expansion_at_low_level_points D HW F Cm, GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm,
    GlobalTheory.T.wachModule_saturated_exactness_crystalline D HW F Cm, GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F, GlobalTheory.T.p8_of_cmpOf D HW F Cm, GlobalTheory.T.wachModule_descent_to_tame_subextension D HW F,
    GlobalTheory.T.wachModule_uniqueness_characterisation D HW F, GlobalTheory.T.gammaSemisimpleQuotientD_statement D HW F Cm, GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F,
    GlobalTheory.NL.FiniteRestrictionH1f.mem_H1f_iff_res_mem D HW F, GlobalTheory.T.wachIntegralComplex_cocycle_class_finite D HW F, GlobalTheory.T.defect_torsion_second_cohomology_kernel D HW F Cm,
    GlobalTheory.T.cokernel_crystalline_surjection_killed_by_X_pow D HW F Cm, ?_⟩
  unfold ConclusionE
  exact ⟨GlobalTheory.NL.NygaardExtension.main D HW F, GlobalTheory.T.local_comparison_of_cmpOf D HW F Cm⟩

end GlobalTheory.NL
