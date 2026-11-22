module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {S : Scheme.{0}} {p p' : σ} (f : S ⟶ X p) (f' : S ⟶ X p') (_ : S), f ≫ Sigma.ι X p = f' ≫ Sigma.ι X p' → p = p' := by
  intro σ X S p p' f f' s h
  have e : Sigma.ι X p (f s) = Sigma.ι X p' (f' s) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact congrArg Sigma.fst ((sigmaι_eq_iff X p p' _ _).mp e)
