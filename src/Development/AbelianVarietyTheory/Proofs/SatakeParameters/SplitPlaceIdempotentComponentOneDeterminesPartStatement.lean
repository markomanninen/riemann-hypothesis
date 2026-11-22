module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPart
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
theorem _root_.GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  first | exact @GlobalTheory.PlaceSupp.comp_idem | exact GlobalTheory.PlaceSupp.comp_idem | (intros; apply GlobalTheory.PlaceSupp.comp_idem <;> assumption)
