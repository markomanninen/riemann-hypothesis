module

public import Mathlib
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEq

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem glRel_EopV : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ), Formalism.REAL.GlRel (EopV π τ) := by
  intro E _ _ _ a π τ i j k l
  have key := GlobalTheory.CompanionTheory.ClozelPurity.EopV_val E a π τ
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  have h := LinearMap.congr_fun (glRel_Eop (a := a) τ i j k l) φ.1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, key] at h ⊢
  split_ifs at h ⊢ <;> simpa [key] using h

end GlobalTheory.CompanionTheory.Clozel
