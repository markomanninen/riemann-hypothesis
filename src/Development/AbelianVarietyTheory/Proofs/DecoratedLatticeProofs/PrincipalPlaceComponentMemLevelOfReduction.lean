module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMoveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelationsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInvStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOneStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductionsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElementStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatchStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

namespace GlobalTheory.LevAssembly

theorem gAt_mem_levG_of_red : ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank), L.P.H = ⊥ → ∀ (g : GA D S), ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → (∀ PP' ∈ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS → Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) → Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g))) = 1 → gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG S βS L := by
  intro D S βS L hH g PP hPP huniq hQ hSt hred hr
  have hone : ∀ PP' : Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) →
      Formalism.L2.DIV.redFn βS PP' (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) = 1 := by
    intro PP' hne
    exact GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS _ PP' hSt (GlobalTheory.AdelicU.proj_emb_ne _ _ hne _)
  refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC S _ _, ?_⟩
  show Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L
  refine ⟨⟨⟨⟨GlobalTheory.LevSplit.finE_mem_UA S _, hSt⟩, ?_⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun PP' => Subgroup.mem_iInf.2 fun hPP' => ?_
    refine Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    by_cases h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
    · rw [huniq PP' hPP' h]; exact hred
    · rw [hone PP' h]; exact Subgroup.one_mem _
  · refine Subgroup.mem_iInf.2 fun PP' => Subgroup.mem_iInf.2 fun hPP' => ?_
    refine Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hone PP' (hQ PP' hPP')]; exact Subgroup.one_mem _
  · show Formalism.L2.DIV.rTup βS L _ ∈ L.P.H
    rw [hH, Subgroup.mem_bot]
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP'.1 _) = 1
    by_cases h : PP'.1.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
    · rw [huniq PP'.1 PP'.2 h]; exact hr
    · rw [hone PP'.1 h]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

end GlobalTheory.LevAssembly
