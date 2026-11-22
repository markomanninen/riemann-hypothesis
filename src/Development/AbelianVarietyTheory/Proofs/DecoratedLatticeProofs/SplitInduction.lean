module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateOneEqStandardLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeChainStandardPair
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateStandardLatticeIsSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIffStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDetRootCharMulStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReadingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.VacConst

theorem suppAt_one {D : D7} (e : Formalism.L2.Theta.AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V 1 := by
  intro i j
  have h : mt V 1 - 1 = 0 := by rw [GlobalTheory.AdelicLatMove.mt_one, sub_self]
  rw [h, Matrix.zero_apply, mul_zero]

theorem split_induction {D : D7} (V : HSp D) (P : GA D V → Prop)
    (hP : ∀ g ∈ GfC V, P g → ∀ e, IsSplitIdem D e → ∀ s, Formalism.L2.Theta.SuppAt e V s → P (s * g))
    {s : GA D V} (hs : s ∈ splitPart V) : s ∈ GfC V ∧ ∀ g ∈ GfC V, P g → P (s * g) := by
  induction hs using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨e, he, hx⟩ := hx
    exact ⟨GlobalTheory.SplitHecke.Stab.mem_GfC he hx, fun g hg h => hP g hg h e he x hx⟩
  | inv_mem x hx =>
    obtain ⟨e, he, hx⟩ := hx
    have hx' := GlobalTheory.SplitHecke.Stab.suppAt_inv hx
    exact ⟨GlobalTheory.SplitHecke.Stab.mem_GfC he hx', fun g hg h => hP g hg h e he _ hx'⟩
  | one => exact ⟨one_mem _, fun g _ h => by rwa [one_mul]⟩
  | mul x y _ _ ihx ihy =>
    refine ⟨mul_mem ihx.1 ihy.1, fun g hg h => ?_⟩
    rw [mul_assoc]
    exact ihx.2 _ (mul_mem ihy.1 hg) (ihy.2 g hg h)

end GlobalTheory.AdForm.VacConst
