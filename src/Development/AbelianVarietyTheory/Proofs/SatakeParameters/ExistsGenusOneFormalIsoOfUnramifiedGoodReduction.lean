module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubTwoOmegaSq
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import ReciprocityTheory.ClassFieldTheory.GlobalClassField.IsFrobAtMulOfMemInertiaGroup
public import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK

@[expose] public section

namespace GlobalTheory.TwV.Lt

theorem curveEx_of_cm (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) : CurveEx := by
  intro D cc δ B χ hc hd hχ p _ hcop h5 hIn lam
  obtain ⟨g, hgl, hAt, hM, hLT⟩ :=
    GlobalTheory.InertGenusOne.datum_exists_coprime h2 h3 D cc δ hc hd p hcop h5 hIn lam
  exact ⟨g, hLT, h5, hAt, hIn, hM, hc, hd, hχ, hgl.symm, hAt.2.2.2.1⟩

theorem exists_genusOne_formal_iso_of_unramified_good_reduction (h : Formalism.L2.Th1.CM.CM2) : CurveEx :=
  curveEx_of_cm h GlobalTheory.HondaCM3.cm3

end GlobalTheory.TwV.Lt
