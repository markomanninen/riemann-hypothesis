module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariant
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

@[expose] public section

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

namespace PositivityTheory.Rg.BcN.F2

open GlobalTheory.PRep (IsSmooth fixed)
open GlobalTheory.SmGL (HasFiniteLength IsSubquotient)

/-- A finite-length smooth representation contains `π` as a subquotient if the Hecke operator
acts non-nilpotently on its `K`-fixed vectors and vanishes on the fixed vectors of every
irreducible smooth subquotient inequivalent to `π`. -/
def SubOfNonNil' : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
    ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ → τ.IsIrreducible →
      IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0) →
    (∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0) → IsSubquotient π ρ

end PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.T

open PositivityTheory.Rg.BcN.F2 (SubOfNonNil') in
open GlobalTheory.CompanionTheory.HeckeSub (exists_iterate_eq_zero_of_subquot) in
/-- A Hecke operator that vanishes on the fixed vectors of all irreducible
subquotients inequivalent to `π` can act non-nilpotently only if `π` occurs. -/
theorem subquotient_of_non_nilpotent_variant : SubOfNonNil' F ι := by
  intro K e hE V _ _ π _ _ U _ _ ρ hρ hfl hkill hNonNilpotent
  by_contra hNotSubquotient
  obtain ⟨r, hIterateZero⟩ :=
    exists_iterate_eq_zero_of_subquot hE π ρ hρ hfl hkill hNotSubquotient (⊤ : Subrepresentation ρ)
  obtain ⟨u, hu, hIterateNeZero⟩ := hNonNilpotent r
  exact hIterateNeZero (hIterateZero u Submodule.mem_top hu)

end GlobalTheory.T
