module

public import Mathlib

@[expose] public section

open scoped BigOperators
open Module

namespace GlobalTheory

section PolynomialFunction

variable (K : Type*) [CommSemiring K] {M : Type*} [AddCommMonoid M] [Module K M]

variable {K}

end PolynomialFunction

section Frames

variable {ι : Type*} {K : Type*} {V : ι → Type*}

section Semiring

variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]

abbrev EntryIndex (m n : ι → Type*) : Type _ := Σ s, m s × n s

def entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) : EntryIndex m n → α :=
  fun k => b k.1 k.2.1 k.2.2

def ofEntries {α : Type*} (ξ : EntryIndex m n → α) : ∀ s, Matrix (m s) (n s) α :=
  fun s => Matrix.of fun i j => ξ ⟨s, i, j⟩

omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_apply {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) (s : ι) (i : m s)
    (j : n s) : entries b ⟨s, i, j⟩ = b s i j := rfl




end Semiring

variable [Fintype ι] {r : ι → ℕ} [Field K] [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
  {W : Type*} [AddCommGroup W] [Module K W]


end Frames

section Hadamard

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

section Inner

variable [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace 𝕜 (V s)]
  [∀ s, FiniteDimensional 𝕜 (V s)]

end Inner

end Hadamard

section PolynomialWeight

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]

noncomputable def detProdPoly (R : Type*) [CommRing R] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] : MvPolynomial (EntryIndex n n) R :=
  ∏ s, (ofEntries MvPolynomial.X s).det

end PolynomialWeight

section HadamardPolynomial

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜]

end HadamardPolynomial

section Gauss

open MvPolynomial IsLocalRing

variable {K Γ O : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
  [CommRing O] [Algebra O K]

variable [IsLocalRing O] [Infinite (ResidueField O)]

variable {ι : Type*} [Fintype ι]

section Matrices

variable {n : ι → Type*} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]

end Matrices

section Lattices

variable {V : ι → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ s, Module O (V s)]
  [∀ s, IsScalarTower O K (V s)] {Λ : ∀ s, Submodule O (V s)}

variable {r : ι → ℕ}

end Lattices

end Gauss

end GlobalTheory
