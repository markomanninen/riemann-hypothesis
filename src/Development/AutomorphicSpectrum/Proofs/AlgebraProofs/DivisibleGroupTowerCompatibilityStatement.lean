module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
open Coalgebra Bialgebra PositivityTheory.HtPt.Twpdiv in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisible_group_tower_compatibility :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C]
      (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
      (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La]
      (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L)
      (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate)
      (hre : X.Realises G e τ),
      (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G,
        (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La),
          (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧
      ∀ (H : PDivGroup p O) (f f' : G ⟶ H),
        (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre
  let ev (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O := (evalAt (X.A n) t).comp (e n).toAlgHom
  have ev_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : ev n t g = (e n g).1 t := rfl
  have ev_sep (n : ℕ) : PositivityTheory.HtPt.Twpdiv.Sep (ev n) :=
    fun _ _ h => (e n).injective (Subtype.ext (funext h))
  have ev_lev (n : ℕ) (a : La) : ev n (lev p n a) = (τ a).pt n :=
    AlgHom.ext fun g => (hre.pt a n g).symm
  have tate_pt {H : PDivGroup p O} (f : G ⟶ H) (a : La) (n : ℕ) (g : H.A n) :
      (tateMap G H O f (τ a)).pt n g = (τ a).pt n (f.app n g) := rfl
  constructor
  · intro φ dφ h
    let levMap (n : ℕ) : LevGrp La p n →* LevGrp La p n :=
      AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ φ.toIntLinearMap (by
        rintro _ ⟨b, rfl⟩
        exact ⟨φ b, (map_nsmul φ _ b).symm⟩)).toAddMonoidHom
    have levMap_lev (n : ℕ) (a : La) : levMap n (lev p n a) = lev p n (φ a) := rfl
    have liftable (n : ℕ) (g : G.A n) : ∃ u : G.A n, ∀ t, ev n t u = ev n (levMap n t) g := by
      let pulled (t : LevGrp La p n) : O := (e n g).1 (levMap n t)
      have hpulled : pulled ∈ X.A n :=
        (h n (e n g).1 pulled fun a => congrArg (e n g).1 (levMap_lev n a)).1 (e n g).2
      let u : X.A n := ⟨pulled, hpulled⟩
      refine ⟨(e n).symm u, fun t => ?_⟩
      rw [ev_apply, AlgEquiv.apply_symm_apply, ev_apply]
    let pull (n : ℕ) : G.A n →ₐ[O] G.A n :=
      Ord.liftTo (ev n) (ev_sep n) (fun t => ev n (levMap n t)) (liftable n)
    have ev_pull (n : ℕ) (t : LevGrp La p n) : (ev n t).comp (pull n) = ev n (levMap n t) :=
      Ord.ev_liftTo _ _ _ _ t
    have pull_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
        ev n t (pull n g) = ev n (levMap n t) g := DFunLike.congr_fun (ev_pull n t) g
    have pull_lev (n : ℕ) (a : La) (g : G.A n) :
        ev n (lev p n a) (pull n g) = ev n (lev p n (φ a)) g := by
      rw [pull_apply, levMap_lev]
    have ev_one (n : ℕ) (g : G.A n) : ev n 1 g = counit (R := O) g := by
      rw [← lev_zero p n, ev_lev, map_zero]
      rfl
    have ev_mul (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
        pair (ev n s) (ev n t) (comul (R := O) g) = ev n (s * t) g := by
      obtain ⟨a, rfl⟩ := lev_surjective p n s
      obtain ⟨b, rfl⟩ := lev_surjective p n t
      rw [← lev_add, ev_lev, ev_lev, ev_lev, map_add]
      exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm
    let app (n : ℕ) : G.A n →ₐc[O] G.A n :=
      BialgHom.ofAlgHom (pull n)
        (AlgHom.ext fun g => by
          change counit (R := O) (pull n g) = counit (R := O) g
          rw [← ev_one, ← ev_one, pull_apply, map_one])
        (AlgHom.ext fun g => (ev_sep n).pair (ev_sep n) _ _ fun z => by
          change pair (ev n z.1) (ev n z.2) (Algebra.TensorProduct.map _ _ (comul (R := O) g)) =
            pair (ev n z.1) (ev n z.2) (comul (R := O) (pull n g))
          rw [pair_map, ev_pull, ev_pull, ev_mul, ev_mul, pull_apply, map_mul])
    let f : G ⟶ G :=
      { app := app
        comm n := BialgHom.ext fun g => ev_sep n _ _ fun t => by
          obtain ⟨a, rfl⟩ := lev_surjective p n t
          calc
            ev n (lev p n a) (G.res n (pull (n + 1) g)) =
                ev (n + 1) (lev p (n + 1) (p • a)) (pull (n + 1) g) := hre.res n _ a
            _ = ev (n + 1) (lev p (n + 1) (φ (p • a))) g := pull_lev (n + 1) (p • a) g
            _ = ev (n + 1) (lev p (n + 1) (p • φ a)) g := by rw [map_nsmul]
            _ = ev n (lev p n (φ a)) (G.res n g) := (hre.res n g (φ a)).symm
            _ = ev n (lev p n a) (pull n (G.res n g)) := (pull_lev n a (G.res n g)).symm }
    refine ⟨f, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_), fun n g a => pull_lev n a g⟩
    rw [tate_pt, ← ev_lev, ← ev_lev]
    exact pull_lev n a g
  · intro H f f' hf
    refine GlobalTheory.PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g => ev_sep n _ _ fun t => ?_)
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    rw [ev_lev, ← tate_pt, ← tate_pt, hf]
