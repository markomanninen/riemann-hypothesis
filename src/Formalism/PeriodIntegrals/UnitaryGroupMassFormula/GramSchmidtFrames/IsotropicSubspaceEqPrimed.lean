module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFdGramCut
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundX
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
public import Formalism.HermitianCurvature.BigCellVanishingOfCommute
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedFrameProperty
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector

@[expose] public section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section defs

variable (k r : ℕ)

def Xsp : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ (Set.range fun a : Fin r => bvec (eI k r a))

def Wsp (z : Fin (2 * r + k + 1) → ℂ) : Set (Fin (2 * r + k + 1) → ℂ) :=
  {v | inWb k r v ∧ herm (Hpk k r) v z = 0}

def wbPart (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0

def prW (z v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  wbPart k r v + (herm (Hpk k r) (wbPart k r v) z / (Tz k r z : ℂ)) • z

def xcof (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ b, (Zhat k r z z' g).adjugate b (Fin.last r) • (g *ᵥ fvec k r z' b)

def xcofL (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a

def omW (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ := prW k r z (xcof k r z z' g)

def omW' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)

end defs

end PI.UnitaryGroupMassFormula.GsFr
