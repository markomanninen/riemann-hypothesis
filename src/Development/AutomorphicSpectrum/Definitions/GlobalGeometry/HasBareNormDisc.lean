module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GeometricComponentEmbedding

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

abbrev FracBase {O : Type} [CommRing O] (β : O →+* c.F) : Prop :=
  Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a

def Reads (U : Set (Xo.XF c)) (τ : E →+* ℂ) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) : Prop :=
  ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c),
    under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U →
    ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) →
      (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) →
      ψ (s p z) = φ F y v w

def UnitRule (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (sig : GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.Rule Y) :
    Prop :=
  ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Y.X) v w,
    GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.IsFrame Y U τ j x v w → IsUnit (sig R x v w)

end GlobalTheory.CompanionTheory.Ar.Br
