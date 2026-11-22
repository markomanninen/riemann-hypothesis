module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullRepTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittakerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsEmbedRegularRepresentationCopieStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPair
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LemmaLSeriesWeightsOfGreenCuspidalParametrisatioStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinearStandardBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesComplexEmbeddStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineMultipleLeFamilyThresholdStatement

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BadWOn

open Module GlobalTheory.BadCount GlobalTheory.TwistedRepresentationEmbedding GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

theorem model_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (T : ℕ)
    (hρ : IsPullRep M ka ρ)
    (hc : (M.p0 = 0 ∨ M.p0 = r) ∨ (0 < M.p0 ∧ M.p0 < r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧ GlobalTheory.ShareOn.sOf M ≤ T ∧
      LevelHyp (GlobalTheory.ShareOn.sub M ⊥)))
    (H P : Subgroup U) (hH : LevelHyp (GlobalTheory.ShareOn.sub M H)) (hP : LevelHyp (GlobalTheory.ShareOn.sub M P)) (lam : P →* ℂˣ) :
    ∃ n : ℕ, EmbReg ρ H n ∧ (n : ℝ) * Nat.card H ≤ 2 * Nat.card P * finrank ℂ (eig ρ P lam) := by
  rcases hc with hdef | ⟨h0, hr, hA, hs, hbot⟩
  · obtain ⟨-, hrest⟩ := GlobalTheory.T.definite_cuspForms_finite_regularRepresentation E r U C M hdef ka ρ hρ
    obtain ⟨⟨n, hn, hnc⟩, -⟩ := hrest H hH
    have hP2 := (hrest P hP).2 lam
    refine ⟨n, hn, ?_⟩
    have e : (n : ℝ) * Nat.card H = Nat.card P * finrank ℂ (eig ρ P lam) := by exact_mod_cast (hnc.trans hP2.symm)
    rw [e]
    have : (0 : ℝ) ≤ Nat.card P * finrank ℂ (eig ρ P lam) := by positivity
    linarith
  · have hR := GlobalTheory.T.twoLevelFlagDomain_cuspForm_ranks_shifted_weights E r U C M hbot h0 hr ka T hA hs
    obtain ⟨n, hn, hb⟩ := GlobalTheory.T.twoLevelCuspForms_embed_regularRepresentation_copies E r U C M ka ρ hρ _ _ hR H hH
    have hS := (GlobalTheory.T.twoLevelFlagDomain_eigenspace_share E r U C M ka ρ hρ _ _ hR P hP lam).1
    refine ⟨n, hn, ?_⟩
    have h4 := hR.2.2.2.1
    have hb' : (n : ℝ) * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) := by
      exact_mod_cast hb
    have hS' : (finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) : ℝ) ≤
        Nat.card P * finrank ℂ (eig ρ P lam) := by exact_mod_cast hS
    calc (n : ℝ) * Nat.card H ≤ _ := hb'
      _ ≤ 2 * finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) := h4
      _ ≤ 2 * (Nat.card P * finrank ℂ (eig ρ P lam)) := by linarith
      _ = 2 * Nat.card P * finrank ℂ (eig ρ P lam) := by ring

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


end Point

end GlobalTheory.BadWOn

end
