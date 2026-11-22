module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
public import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

@[expose] public section

open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section
namespace GlobalTheory.InertOfConj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

end GlobalTheory.InertOfConj
