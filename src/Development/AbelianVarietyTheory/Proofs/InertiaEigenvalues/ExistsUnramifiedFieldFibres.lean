module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunction
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefined
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugation
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.DetFibre

section Periods

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Periods

section Marks

open GlobalTheory.CharRead

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem det_cong_of_finCong (V : HSp D) (N : ℕ) (hN : N ≠ 0) (u : GA D V) (hu : FinCong V N u) :
    ∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (N : ℕ) • w := by
  obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  exact det_cong_one D.host.F (latC V) k3 k4 N hN (finHom V u).1 (by rw [← k1]; exact hu)





end Marks


end GlobalTheory.DetFibre
