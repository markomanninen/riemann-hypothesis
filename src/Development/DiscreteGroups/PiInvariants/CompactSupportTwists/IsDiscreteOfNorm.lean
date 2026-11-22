module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace DiscreteGroups.T1.G

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


theorem reg_of {π : CuspSub E n} (hreg : (CG.mk π).IsRegAlg) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : HasInfCharGL π.V τ m) : ∃ lam : DomWeight n, m = infOfWeight lam := by
  have h1 : (CG.mk π).HasInfChar τ m := hm
  obtain ⟨hnd, hz⟩ := hreg τ
  rw [h1.infChar_eq] at hnd hz
  obtain ⟨lam, hl⟩ := GlobalTheory.WtComb.exists_domWeight_infOf n m hm.1 hnd hz
  exact ⟨lam, hl.symm.trans (GlobalTheory.UnitaryReadTrue.infOf_eq_infOfWeight lam)⟩

end DiscreteGroups.T1.G

end
