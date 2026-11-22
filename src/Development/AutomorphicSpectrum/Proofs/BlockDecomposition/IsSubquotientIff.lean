module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import GroundTheory.AutomorphicForms.FiniteLengthJacquet

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OnePart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hasSat_iff {π : CuspSub E n} {w : HeightOneSpectrum (𝓞 E)} {τ : SmIrr (GL (Fin n) (w.adicCompletion E))}
    (hτ : π.IsLocComp w τ) (B : Multiset ℂˣ) : (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w τ.ρ B := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  obtain ⟨α, hαB, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π h hτ
  rw [← hαB]
  exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n _ _ _ hα

end GlobalTheory.CompanionTheory.OnePart

end
