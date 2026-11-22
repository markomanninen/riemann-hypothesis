module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffWordModerateGrowthBound
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffWord_moderateGrowth_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (f : Mx n → ℂ) (F : List (Mx n) → Mx n → ℂ),
    (∀ g ∈ UJset ε, F [] g = f g) → IsDerFam ε F → FamGrowth ε N F →
    ∀ u : List (Ltr ε), ∃ C : ℝ, ∀ g ∈ UJset ε, ‖wordF u f g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N := by
  first | exact @GlobalTheory.TypeSum.CoefClos.wordF_growth | exact GlobalTheory.TypeSum.CoefClos.wordF_growth | (intros; apply GlobalTheory.TypeSum.CoefClos.wordF_growth <;> assumption)
