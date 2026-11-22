module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerTheoremOfLocalComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepOnEqOfEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLCoeffMapFunctorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLSaturatedOfSelmerSetupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerFunctorLeftExactTorsionCoefficientsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionLeftExactFunctorKernelSquareMatrixStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelFun

theorem oneMatrix_of_galoisCohomology :
    Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness →
    LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar →
    UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching →
    ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
      (bkP : BKPh X), ThmS bkP := by
  intro _ hPT hCD _ hLF hLT hLE hGF hGE _ hadm D N X bkP
  refine GlobalTheory.T.selmer_theorem_of_local_components GlobalTheory.T.torsion_left_exact_functor_kernel_square_matrix D N X bkP ?_
  intro i s Λ _ _ _ κ Q hS
  have hN := GlobalTheory.T.noGaloisInvariantsTorsionCoeff_of_selmerSetup D N X bkP i s Λ κ Q hS
  have hU := GlobalTheory.T.localConditionAboveLSaturated_of_selmerSetup hLF hLT hLE hadm D N X bkP i s Λ κ Q hS
  have hC := GlobalTheory.T.local_count_of_setup hLF hLT hLE hadm D N X bkP i s Λ κ Q hS
  exact ⟨GlobalTheory.SelFun.selMaps D N X bkP i s Λ κ Q,
    GlobalTheory.T.selmer_functor_left_exact_torsion_coefficients D N X bkP i s Λ κ Q hS hN hU,
    GlobalTheory.SelFun.Colim.selColim D N X bkP i s Λ κ Q hS hN hU,
    GlobalTheory.T.selmerObstruction_le_residualSelmer_simpleExtension hPT hCD hLF hLT hLE hGF hGE D N X bkP i s Λ κ Q hS hN hU hC⟩

end GlobalTheory.SelFun
