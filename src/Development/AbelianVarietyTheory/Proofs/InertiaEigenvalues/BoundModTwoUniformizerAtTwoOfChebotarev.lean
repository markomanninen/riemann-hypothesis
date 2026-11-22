module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValLeOfNotMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleChangeScalarsBack
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntiOfKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDualStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerPresentationMatrixOfGaloisCohomology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastEqOneOfMod

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.Dyadic

theorem bound_mod_two_of_hypothesis : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmC bkP := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hS := GlobalTheory.SelFun.oneMatrix_of_galoisCohomology h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hgw := GlobalTheory.T.residual_selmer_finrank_eq_dual h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hk4 := GlobalTheory.ScalarFrob.firstHalf h5 h6 h7 h4 D N X bkP
  refine GlobalTheory.StepTwo.TwoBound.thmC_of_parts D N X bkP (GlobalTheory.ChosenPrimes.stepAB h1 D N X) (fun i => GlobalTheory.ChooseForms.chooseH h8 D N X bkP i fun s hs =>
    ⟨GlobalTheory.ResSel.SpanOddPf.spanOdd D N X bkP i s hs, GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp D N X bkP i s hs, hgw i s hs⟩) fun i s hs => ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.StepTwo.StartInd.start_of_resBound D N X bkP i s hs (GlobalTheory.ScalarFrob.firstPlace h5 h6 h7 D N X bkP i s hs) (GlobalTheory.ResOrder.resBound h4 D N X bkP i s hs (hk4 i s hs)
      (GlobalTheory.ResRecip.reciprocity h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP i s hs (hk4 i s hs)) (hgw i s hs))
  · exact GlobalTheory.Growth.grow h4 D N X bkP hS i s hs
  · exact GlobalTheory.NewPrime.step h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP hS i s hs

end GlobalTheory.StepTwo.Dyadic
