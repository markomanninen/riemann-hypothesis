module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtensionStatement

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.landherr_and_landherrSt :
    _root_.GlobalTheory.Published.Landherr ∧ _root_.GlobalTheory.Published.LandherrSt :=
  ⟨_root_.GlobalTheory.LocalQuad.landherr_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt,
    _root_.GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt⟩

end GlobalTheory.QNorm
