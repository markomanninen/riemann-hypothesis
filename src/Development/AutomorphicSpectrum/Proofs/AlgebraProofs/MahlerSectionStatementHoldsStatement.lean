module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ValNeBot
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP

@[expose] public section

open MvPolynomial NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Short ReciprocityTheory.ChartRestriction.G.T0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_section_statement_holds : GroundTheory.Heights₂.Heights.MahlerSection.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.mahlerSection | exact GlobalTheory.CompanionTheory.Ar.Short.mahlerSection | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.mahlerSection <;> assumption)
