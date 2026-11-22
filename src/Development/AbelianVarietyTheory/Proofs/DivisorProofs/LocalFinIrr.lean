module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugacyClassClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCentralizerTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompactStatement

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.LocFinIrr

def conjMA (H : Type*) [Group H] : MulAction H H where
  smul g y := g * y * g⁻¹
  one_smul y := by show 1 * y * 1⁻¹ = y; group
  mul_smul a b y := by show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹; group

theorem conjMA_cont (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    @ContinuousSMul H H (conjMA H).toSMul _ _ :=
  @ContinuousSMul.mk H H (conjMA H).toSMul _ _ (by
    show Continuous fun q : H × H => q.1 * q.2 * q.1⁻¹
    fun_prop)

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.OrbFinAf.LocFinIrr
