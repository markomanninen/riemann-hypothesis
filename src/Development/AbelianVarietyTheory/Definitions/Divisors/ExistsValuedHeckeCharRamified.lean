module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.Model

section General

variable {E : Type} [Field E] [NumberField E]

theorem IsCMType.bijective {I : Type} {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm

end General

section Integrality

end Integrality

section Symmetry

variable {E : Type} [Field E] [NumberField E]

end Symmetry

section Twist

variable {E : Type} [Field E] [NumberField E]

end Twist

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end CM

section Cyclotomic


end Cyclotomic

end GlobalTheory.CMVal.Model
