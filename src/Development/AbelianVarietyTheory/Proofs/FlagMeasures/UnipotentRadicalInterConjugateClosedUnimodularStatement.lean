module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular : ∀ (k r : ℕ) (γ : Mat k r), γ ∈ GG k r → IsClosedSub k r (Rset k r γ) ∧ ∀ μ, IsHaarOn (Rset k r γ) μ → IsUnimod (Rset k r γ) μ := by
  first | exact @GlobalTheory.UnipUnimod.rset_unimodular | exact GlobalTheory.UnipUnimod.rset_unimodular | (intros; apply GlobalTheory.UnipUnimod.rset_unimodular <;> assumption)
