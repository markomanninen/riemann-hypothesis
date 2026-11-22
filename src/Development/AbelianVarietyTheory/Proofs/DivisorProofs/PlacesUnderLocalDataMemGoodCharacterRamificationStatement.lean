module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesUnderLocalDataMemGoodCharacterRamification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRankStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridSquareRankInequalitiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStandingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinsetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCharactersIsGoodGridPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelConjugateDoubledStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareModelNegSpaceGoodSchroedingerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepDualPairCharactersBetaQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepSquarePairCharactersAlphaQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBasePStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirstStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevelStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB alpha beta blk)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf HasExp SplitsFully)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placesUnder_localData_mem_goodCharacter_ramification : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (a a' : ℕ),
    X.α = alpha G t i j → X.β = beta G i j → X.IsGood B a a' →
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ X.T := by
  first | exact @GlobalTheory.BigNZ.LocalPlaceUnderMembership.under_locPl_mem | exact GlobalTheory.BigNZ.LocalPlaceUnderMembership.under_locPl_mem | (intros; apply GlobalTheory.BigNZ.LocalPlaceUnderMembership.under_locPl_mem <;> assumption)
