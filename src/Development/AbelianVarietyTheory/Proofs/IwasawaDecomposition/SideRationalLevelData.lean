module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicModularFormsIrreducibleDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigensystemMultiplicities
public import Formalism.LocalToGlobal.UnitaryNorms.CharShare
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyResidualImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVEqAbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfTypeSpaceNeBotOfIsotypicPartStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompactOpenMembership
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


open Classical in
noncomputable def GlobalTheory.AutPart.jumpOf (a : ℕ) (z : ℂ) : ℤ :=
  if h : ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 then -h.choose else 0

theorem GlobalTheory.AutPart.jumpOf_spec (a : ℕ) (z : ℂ) (h : ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    ((GlobalTheory.AutPart.jumpOf a z : ℤ) : ℂ) = -z + ((a : ℂ) - 1) / 2 := by
  unfold GlobalTheory.AutPart.jumpOf
  rw [dite_eq_left h]
  conv_rhs => rw [h.choose_spec]
  push_cast; ring

