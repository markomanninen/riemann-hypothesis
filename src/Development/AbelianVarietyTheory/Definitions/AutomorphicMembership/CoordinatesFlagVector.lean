module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle

@[expose] public section

noncomputable section

namespace GlobalTheory.IntPair

open NumberField Matrix Formalism.BasicNotions Formalism.HermitianLatticeCounting.S6 GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntTerm GlobalTheory.SA
open GlobalTheory.HermLat (perp rs smulLat imLat isomGrp mem_isomGrp IsUnimod)

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r g : ℕ}

def co (x : S.V) : Fin S.rank → E := S.frame.equivFun x

variable {S} {T T' : E} {A : Matrix (Fin S.rank) (Fin (r + 1)) E} {Λ Λ₁ : Submodule (𝓞 E) (Fin S.rank → E)}
  {s t : S.V ≃ₗ[E] S.V} {F F' G : FlagD (ofHSpace S) r}

end GlobalTheory.IntPair

end
