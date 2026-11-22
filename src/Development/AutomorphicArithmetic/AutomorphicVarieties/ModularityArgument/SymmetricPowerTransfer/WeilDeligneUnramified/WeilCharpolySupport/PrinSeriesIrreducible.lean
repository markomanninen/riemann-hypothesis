module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UnlFull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open GlobalTheory.TypeTwo.PowIrrProof

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem prinSeries_irreducible {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : ∀ i j, ω j ≠ ω i * absPow k 1) : (prinSeries ω).IsIrreducible := by
  let x : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ω i) (hω i)
  have hx : ∀ i, (x i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (x i).1 = n := by
    show ∑ _i : Fin n, 1 = n
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hnu : ∀ i j, x j ≠ (x i).nu 1 := fun i j e => by
    simp only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
    exact h i j e
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (x i) (hx i)) x hd
      (fun i j => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx i) (hx j) (hnu i j) (hnu j i))
      (fun i => (single_spec (hx i)).2.1)
  let e₀ := Equiv.sigmaUnique (Fin n) fun _ => Fin 1
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ e₀ (stdBlocks (fun i => (x i).1) hd) _).1
    (piTensor fun i => detRep (Fin 1) (ω i))
  have hM : (multiProd e₀ fun i => detRep (Fin 1) (ω i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv
      (p.trans (multiProdEquiv (stdBlocks (fun i => (x i).1) hd)
        fun i => equivRep (IrrRep.det (Fin 1) (ω i) (hω i)))).symm hP
  letI hInd : Nontrivial (IndSp e₀ (piTensor fun i => detRep (Fin 1) (ω i))) :=
    nontrivial_of_irreducible hM
  have nontrivial_sub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
      [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
      (h : IsSubquotient σ ρ) [Nontrivial W] : Nontrivial V := by
    obtain ⟨S, f, hf⟩ := h
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  haveI := @nontrivial_sub _ _ _ _ _ _ _ _ _ _
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e₀ ω) hInd
  have equiv_sub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
      [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
      (h : IsSubquotient σ ρ) [Nontrivial W] (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨E⟩ := equiv_sub (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hM

end Loc

theorem psOf : PsOf := by
  intro _ L _ _ n w τ hT
  haveI : CharZero (w.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hT
  have hs' : HasSupport τ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred).symm
  have hmem : ∀ i, IrrGL.ofChar (ξ i) (hξ i) ∈ GlobalTheory.RoadU.chars ξ hξ := fun i =>
    Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  have hne : ∀ i j, ξ j ≠ ξ i * absPow (w.adicCompletion L) 1 := fun i j e => by
    refine hu _ (hmem j) _ (hmem i) ?_
    simp only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    exact e
  obtain ⟨hi, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds _ n τ.V τ.ρ ξ hξ).1 hs'
  obtain ⟨E⟩ := hq.nonempty_equiv hi (prinSeries_irreducible ξ hξ hne)
  exact ⟨ξ, hξ, ⟨E.symm⟩, fun i j => hne j i⟩

end UpperTheory.V.Z.Sym.W
