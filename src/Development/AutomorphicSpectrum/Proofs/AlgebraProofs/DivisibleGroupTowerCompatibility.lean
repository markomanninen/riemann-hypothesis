module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.LevMapLev

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

open Coalgebra Bialgebra PositivityTheory.HtPt.Gi PositivityTheory.HtPt.Twpdiv in
theorem tower_end_pdiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G, (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧ ∀ (H : PDivGroup p O) (f f' : G ⟶ H), (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre
  let ev (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O :=
    (evalAt (X.A n) t).comp (e n).toAlgHom
  have ev_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : ev n t g = (e n g).1 t := rfl
  have sep (n : ℕ) : Sep (ev n) := fun _ _ h => (e n).injective (Subtype.ext (funext h))
  have ev_lev (n : ℕ) (a : La) : ev n (lev p n a) = (τ a).pt n :=
    AlgHom.ext fun g => (hre.pt a n g).symm
  refine ⟨?_, ?_⟩
  · intro φ dφ h
    have exists_pullback (n : ℕ) (g : G.A n) :
        ∃ g' : G.A n, ∀ t, ev n t g' = ev n (levMap p n φ t) g := by
      refine ⟨(e n).symm ⟨fun t => (e n g).1 (levMap p n φ t), ?_⟩, ?_⟩
      · exact (h n (e n g).1 _ fun _ => rfl).1 (e n g).2
      · intro t
        rw [ev_apply, AlgEquiv.apply_symm_apply]
        rfl
    let pull (n : ℕ) : G.A n →ₐ[O] G.A n :=
      Ord.liftTo (ev n) (sep n) (fun t => ev n (levMap p n φ t)) (exists_pullback n)
    have comp_pull (n : ℕ) (t : LevGrp La p n) :
        (ev n t).comp (pull n) = ev n (levMap p n φ t) := Ord.ev_liftTo _ _ _ _ t
    have ev_pull (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
        ev n t (pull n g) = ev n (levMap p n φ t) g := DFunLike.congr_fun (comp_pull n t) g
    have ev_one (n : ℕ) (g : G.A n) : ev n 1 g = counit (R := O) g := by
      rw [← lev_zero, ev_lev, map_zero]
      rfl
    have ev_mul (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
        pair (ev n s) (ev n t) (comul (R := O) g) = ev n (s * t) g := by
      obtain ⟨a, rfl⟩ := lev_surjective p n s
      obtain ⟨b, rfl⟩ := lev_surjective p n t
      rw [← lev_add, ev_lev, ev_lev, ev_lev, map_add (f := τ)]
      exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm
    let app (n : ℕ) : G.A n →ₐc[O] G.A n :=
      BialgHom.ofAlgHom (pull n)
        (AlgHom.ext fun g => by
          change counit (R := O) (pull n g) = counit (R := O) g
          rw [← ev_one, ← ev_one, ev_pull, map_one])
        (AlgHom.ext fun g => (sep n).pair (sep n) _ _ fun z => by
          change pair (ev n z.1) (ev n z.2)
              (Algebra.TensorProduct.map (pull n) (pull n) (comul (R := O) g)) =
            pair (ev n z.1) (ev n z.2) (comul (R := O) (pull n g))
          rw [pair_map, comp_pull, comp_pull, ev_mul, ev_mul, ev_pull, map_mul])
    let f : G ⟶ G := {
      app := app
      comm n := BialgHom.ext fun g => sep n _ _ fun t => by
        obtain ⟨a, rfl⟩ := lev_surjective p n t
        change (e n (G.res n (pull (n + 1) g))).1 _ = ev n _ (pull n (G.res n g))
        rw [hre.res, ← ev_apply, ev_pull, levMap_lev, ev_apply, ev_pull, levMap_lev,
          ev_apply, hre.res, map_nsmul] }
    have app_eval (n : ℕ) (g : G.A n) (a : La) :
        (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a)) :=
      ev_pull n (lev p n a) g
    refine ⟨f, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_), app_eval⟩
    rw [tateMap_pt, hre.pt, hre.pt, app_eval]
  · intro H f f' hf
    refine PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g => sep n _ _ fun t => ?_)
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    rw [ev_lev, ← tateMap_pt, ← tateMap_pt, hf]

end GlobalTheory.CompanionTheory.Ar.HT
