module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients

@[expose] public section

noncomputable section

namespace GlobalTheory.GoodLatCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

section Clause

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G']


end Clause

section Forms

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
  [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G]

end Forms

section Local

variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

end Local

structure PlaceIso (D : D7) (Pg : Finset (Pl D.host.E)) where
  pl : TypePl D ≃ ↥Pg
  iso : ∀ v : TypePl D, ZMod (D.host.g v.1) ≃+* kP (pl v).1

namespace PlaceIso

variable {D : D7} {Pg : Finset (Pl D.host.E)} (P : PlaceIso D Pg) {LL : Type} [Field LL]

end PlaceIso

section Places

open scoped Pointwise

variable {D : D7}

variable {T : Core D} (hb : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal)
include hb

end Places


open GlobalTheory.MemN.TypesInhab in
theorem goodSeriesIdempotent_central_idempotent (D : D7) :
    D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) ∧ D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  obtain ⟨hc, hm⟩ := good_sum (I := TypePl D) (P := fun v => Fin D.R.r → ZMod (D.host.g v.1))
    (fun v p => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) D.ntypes.e0 (fun g => rfl)
    (fun _ _ => D.ntypes.eSer_idem _ _) (fun _ _ => D.ntypes.eSer_central _ _)
    (fun _ p q hpq => D.ntypes.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))
  refine ⟨hc, ?_⟩
  have h : D.ntypes.e0 = ∑ a : ∀ v : TypePl D, Fin D.R.r → ZMod (D.host.g v.1),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ten (fun v => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf (a v))) else 0 := by
    ext g
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine (finsum_eq_sum_of_fintype _).trans (Finset.sum_congr rfl fun a _ => ?_)
    split_ifs <;> rfl
  conv_lhs => rhs; rw [h]
  rw [Finset.mul_sum]
  conv_rhs => rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [hm, if_pos ha]
  · rw [mul_zero]

theorem isCentralIdempotent_of_goodSeriesIdempotent {D : D7} {LL : Type} [Field LL] (σ₀ : LL →+* ℂ) {eC : G0g D.nd → LL}
    (h : ∀ g, σ₀ (eC g) = D.ntypes.e0.coeff g) : IsCentralIdem eC := by
  obtain ⟨hc, hi⟩ := goodSeriesIdempotent_central_idempotent D
  refine ⟨fun g x => σ₀.injective ?_, fun g => σ₀.injective ?_⟩
  · have := congrArg (fun z => z.coeff (x * g))
      (Subalgebra.mem_center_iff.1 hc (MonoidAlgebra.single x (1 : ℂ)))
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, inv_mul_cancel_left, one_mul, mul_one] at this
    rw [h, h, this]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, h, ← hi, GlobalTheory.MemN.TypesInhab.coeff_mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul, h, h]

section Sides

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
  (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

end Sides

end GlobalTheory.GoodLatCompare
