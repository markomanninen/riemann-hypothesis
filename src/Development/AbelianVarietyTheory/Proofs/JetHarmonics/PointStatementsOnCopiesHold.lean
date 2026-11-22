module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetsOnCopiesOfCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsUnitOfPrimeNe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermOfFamHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowPELOfLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTermLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsTer
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowGerm

theorem pointStatements_on_copies :
    RPointT ∧ GenPointT ∧ JetsOnCopiesCompatibleFrames ∧ GermOfFamT ∧ ThetaFrameF ∧ PowPELF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have ht := GlobalTheory.twistBaseChange_and_valuation_statements.1
  exact ⟨GlobalTheory.SmallTranslate.main h1 h2 h3 h4 h5 ht,
    GlobalTheory.GeneratorsAtPoint.main h1 h2 h3 h4 h5 ht,
    GlobalTheory.PowJets.jets_on_copies h1 h2 h4 ht,
    GlobalTheory.PowGerm.germOfFam_holds h1 h2 h4 ht,
    GlobalTheory.PowThetaFrame.main h1 h2 h4 ht,
    GlobalTheory.PowGerm.powPEL_of_laws h1 h2 h3 h4 h5 ht⟩

end GlobalTheory.PowGerm
