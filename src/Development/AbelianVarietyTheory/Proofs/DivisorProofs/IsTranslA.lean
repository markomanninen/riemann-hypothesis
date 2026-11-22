module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubAFiniteFree

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def IsTranslA (f : D.La →+ D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ (∀ x, o'.eta x = o.eta (f x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSubA o f N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

end GlobalTheory.UPel.HT.HeckeAd
