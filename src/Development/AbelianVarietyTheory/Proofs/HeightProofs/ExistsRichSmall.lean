module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipal
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzAdjoinRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzFieldRangeEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRootStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostXiOrderBounds
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem weberSet_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) : weberSet L n = weberSet L' n := by
  have hG : ∀ k, L.G k = L'.G k := fun k => by unfold PeriodPair.G; rw [h]
  have h2 : L.g₂ = L'.g₂ := by unfold PeriodPair.g₂; rw [hG]
  have h3 : L.g₃ = L'.g₃ := by unfold PeriodPair.g₃; rw [hG]
  have hP : ∀ z, L.weierstrassP z = L'.weierstrassP z := fun z => by unfold PeriodPair.weierstrassP; rw [h]
  unfold weberSet
  simp only [h2, h3, hP, h]

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
