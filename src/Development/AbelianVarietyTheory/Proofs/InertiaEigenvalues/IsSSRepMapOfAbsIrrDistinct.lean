module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationUniqueUpToConj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces

@[expose] public section

noncomputable section

namespace GlobalTheory.ConstituentsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

open Polynomial Formalism.ConjugateSelfDual

def BrauerNesbitt : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹

section Rep

variable {k Γ : Type} [Field k] [Group Γ]

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

variable {D i}

end Loc

end GlobalTheory.ConstituentsCompare

end
