module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PrimSplit

variable {D : D7}

theorem pX_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) :
    (d.pX *ᵥ colMul d.jX i a) i = a := by
  have e : d.pX *ᵥ colMul d.jX i a = colMul (d.pX * d.jX) i a := by
    funext k
    simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hp : d.pX * d.jX = 1 := by
    have h := congrArg rat d.e'e
    rw [rat_one] at h
    simpa only [HypDec.pX, HypDec.qX, HypDec.jX, rat, Matrix.map_mul] using h
  rw [e, hp, colMul, Matrix.one_apply_eq, mul_one]

theorem idAt_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {P : Pl D → Prop} {i : Fin ρ} {a : AE D}
    (h : colMul d.jX i a ∈ latV S L P) : a ∈ idAt D P := by
  rw [← pX_colMul d i a]
  exact GlobalTheory.IwaPlace.mulVec_mem_idAt _ (GlobalTheory.FinPl.FrameLat.latV_supp h) i

end GlobalTheory.SeeSaw.PrimSplit
