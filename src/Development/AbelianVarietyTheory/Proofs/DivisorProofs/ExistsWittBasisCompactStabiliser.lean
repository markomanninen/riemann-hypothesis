module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermIsUnitGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFactorisationDoubledUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelUnipotentAntidiagonalCorner
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.SWLit.LinAct

section Alg

variable {R : Type} [CommRing R]

variable {A : Type} [CommRing A] [Algebra R A] {α β ν X : Type} [Fintype β] [DecidableEq β]
  [AddCommGroup X] [Module R X] (e : ν ⊕ ν ≃ α)

def Del (w : Matrix α β A) : Prop := ∀ i, w (e (.inl i)) = w (e (.inr i))

def Nab (w : Matrix α β A) : Prop := ∀ i, w (e (.inl i)) = -w (e (.inr i))



variable [Invertible (2 : R)] {e} {D : Matrix α β A ≃ₗ[R] X × X} (hΔ : ∀ w, Del e w → (D w).1 = 0) (hN : ∀ w, Nab e w → (D w).2 = 0)
include hΔ hN

end Alg

end GlobalTheory.SWLit.LinAct

end
