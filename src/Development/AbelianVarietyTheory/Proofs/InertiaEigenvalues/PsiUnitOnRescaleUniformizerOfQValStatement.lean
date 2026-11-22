module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiUnitOn_rescale_uniformizer_of_qVal : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V) (ϖ : T.V), Irreducible ϖ → ∀ (y : D.X) (n : ℤ), QVal D ϖ y n → ∀ q : D.X → (FractionRing T.V)ˣ, (q y : FractionRing T.V) = algebraMap T.V (FractionRing T.V) ϖ ^ (-n) → PsiUnitOn (GlobalTheory.TauTwist.rescale D q) y Set.univ := by
  first | exact @GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal | exact GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal | (intros; apply GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal <;> assumption)
