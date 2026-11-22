module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NotLargeBaseConditionDisjoint
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnitaryRealisationReadingOfIdempotentActsViaLeve
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsEOfHeq

@[expose] public section

noncomputable section

namespace GlobalTheory.NRows.AtPt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem of_is {𝒮 : Slots} {K : Ctx} {q : WPt 𝒮 K} {D : D7} {O : Obj D} (h : q.Is D O) {r : ∀ D : D7, Obj D → Prop}
    (hr : r (q.w.D q.Z) q.O) : r D O :=
  (congrArg (fun x : Σ D : D7, Obj D => r x.1 x.2) h).mpr hr

theorem linkedBundleProperty_after_largeBaseCoreProperty {KP : BaseP} {Q Q' R : V4.Slot} {Bd : BdT} {Lk : LkT Bd} {E : Par → BdP Bd} (h : LargeBaseConditionG KP Q R)
    (he : RowE (sAnd Q' R) Lk E) : Lg1 KP Q Q' fun U => RowE U Lk E :=
  ⟨_, GlobalTheory.Fc.LgModel.largeBaseProperty_conditional (R := R),
    ((EvP.of_evGd h).and he).mono fun _ _ _ t β q c b l => t.2 β ⟨q.1, q.2 t.1⟩ c b l⟩

end GlobalTheory.NRows.AtPt

end
