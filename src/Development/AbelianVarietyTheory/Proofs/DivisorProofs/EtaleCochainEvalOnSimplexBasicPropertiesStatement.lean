module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
      ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
      ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  intro R _ E I n
  have ev_eq {F : Spc} {J : Cx R} (α : Cochain ((chains R).obj F) J n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx F p U) :
      ev α p s h U x = Sec.map ((chainsXIso R F p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α β p s h U x
    have hadd (a b : Cochain ((chains R).obj E) I n) :
        ev (a + b) p s h U x = ev a p s h U x + ev b p s h U x := by
      simp [ev, Cochain.add_v]
    let eval : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
      AddMonoidHom.mk' (fun a => ev a p s h U x) hadd
    exact ⟨hadd α β, map_sub eval α β, map_zero eval, fun c => map_zsmul eval c α⟩
  · intro α p s h V U g x
    rw [ev_eq, CupSpec.map_res, CupSpec.freeGen_res]
    rfl
  · intro α β H
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact CupSpec.free_ext _ _ (fun U x => H k s hs U x)
    · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
  · intro E' f α p s h U x
    rw [ev_eq, ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      ← Category.assoc, CupSpec.chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h)
      (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  · intro J m α p s h U x
    rw [ev_eq, ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      ← Category.assoc]
    rfl
