module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSchemeRepresentingEtaleLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelGroupAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLevelStructureAtGeometricPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.LevForget

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def forgetMap {b : Base D R} {N' : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N' s'}
    {o : Obj b N' s} {f : S' ⟶ S} (m : ObjMap o' o f) (N : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) :
    ObjMap (o'.forget N hd hc) (o.forget N hd hc) f :=
  ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, fun y => m.eta _⟩

end GlobalTheory.UPel.HT.EtLev.LevForget
