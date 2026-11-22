module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProofStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamClosing

theorem keyFam_one : KeyFam fun _ => 1 :=
  GlobalTheory.KeyFamOfExact.keyFam_of_keyFormula GlobalTheory.T.exactKeyFormula_proof

end GlobalTheory.KeyFamClosing
