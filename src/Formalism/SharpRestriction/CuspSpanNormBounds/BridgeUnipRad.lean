module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Mathlib
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.EnergyIdentity
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeUnipRad

open MeasureTheory NumberField Matrix
open Formalism.MainNotions.S

section CM

variable (I : AutInst)

theorem emb_star (v : InfinitePlace I.F) (x : I.E) : I.φ v (star x) = starRingEnd ℂ (I.φ v x) := by
  obtain ⟨hcm, -, -, -⟩ := I.cm
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hcm
  exact hcm.2.1 (I.φ v) x

end CM

section Form

variable {n : ℕ}

theorem hform_eq (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  rw [Formalism.UG.hform.eq_1]
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

end Form

section Span

variable (I : AutInst)

end Span

section Rad

variable {n : ℕ}

variable {J' : Matrix (Fin n) (Fin n) ℂ} {U : Submodule ℂ (Fin n → ℂ)}

end Rad

section Sub

variable {n : ℕ} (ε : Fin n → Bool) {P J' : Matrix (Fin n) (Fin n) ℂ}

end Sub

end Formalism.MainNotions.BridgeUnipRad

end
