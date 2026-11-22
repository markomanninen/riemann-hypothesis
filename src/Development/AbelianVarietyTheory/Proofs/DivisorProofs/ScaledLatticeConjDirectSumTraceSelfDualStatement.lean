module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeConjDirectSumTraceSelfDual
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
theorem _root_.GlobalTheory.T.scaledLattice_conj_directSum_trace_selfDual : ∀ {D : D7} (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e ↔
      ∀ x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (skewGram A B e) y x)) := by
  first | exact @GlobalTheory.SkewLat.pairLat_conj_trace_selfDual | exact GlobalTheory.SkewLat.pairLat_conj_trace_selfDual | (intros; apply GlobalTheory.SkewLat.pairLat_conj_trace_selfDual <;> assumption)
