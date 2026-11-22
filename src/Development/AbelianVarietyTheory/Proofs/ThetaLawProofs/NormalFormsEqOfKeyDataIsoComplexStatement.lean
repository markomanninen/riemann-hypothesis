module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalForms_eq_of_keyDataIso_complex : ∀ x x' : KeyIn ℂ, KeyPB x' x (RingHom.id ℂ) → (∀ t, Val x t ↔ Val x' t) ∧ ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), Nrm x τ a b ↔ Nrm x' τ a b := by
  first | exact @GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff | exact GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff | (intros; apply GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff <;> assumption)
