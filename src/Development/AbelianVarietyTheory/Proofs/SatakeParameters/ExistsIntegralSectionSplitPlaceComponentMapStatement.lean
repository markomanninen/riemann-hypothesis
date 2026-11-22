module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMap
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralSection_splitPlace_componentMap : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  first | exact @GlobalTheory.SplitComp.proj_tensCast_section | exact GlobalTheory.SplitComp.proj_tensCast_section | (intros; apply GlobalTheory.SplitComp.proj_tensCast_section <;> assumption)
