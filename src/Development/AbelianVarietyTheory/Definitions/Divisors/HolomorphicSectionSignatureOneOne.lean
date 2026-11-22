module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRule
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.ExistsCtxOkOfPins
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDictModel

open GlobalTheory.HolDict

section Local

open ReciprocityTheory.ChartRestriction.G.FD

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

end Local

section Adelic

variable {D : D7}

theorem fix_iff (τ : D.host.E →+* ℂ) :
    τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD ↔ ∃ ρ, τ = tauE D ρ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
  have h1 : D.host.galE (D.host.sigmaOf g) = g :=
    (D.host.gal).apply_symm_apply g
  refine Iff.trans ?_ (Formalism.L2.Geo.exists_tauEmb_iff D g).symm
  conv_rhs => rw [← h1]
  refine Iff.trans ?_ (D.host.galE_mem_Psi_iff _).symm
  exact ⟨fun h => D.host.φ₀.injective h, fun h => congrArg D.host.φ₀ h⟩

end Adelic

section Dict

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member

variable {D : D7}


end Dict

section Forms

variable {D : D7}


end Forms

end GlobalTheory.HolDictModel
