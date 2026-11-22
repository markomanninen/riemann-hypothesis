module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBesUnscaledDual

@[expose] public section

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

section Frame

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : Formalism.BasicNotions.TH.HSp D}

theorem besVec_ne_zero (B : SBes X h u ψ A) : B.d.i₀ *ᵥ vecB B.o B.ζ ≠ 0 := fun h0 => by
  apply B.line.2
  have e : B.L.gram *ᵥ B.ζ = (B.o.iBᴴ * (B.d.i₀ᴴ * (D.sp.Y 0).gram)) *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) := by
    rw [← B.o.isoB, ← B.d.iso]
    simp only [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, h0]; simp

end Frame

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def InPlace : Prop := Placed f B ∧ Framed B

variable {f B}

variable (f B)

theorem shift_tOf (a₀ a : GA D (D.sp.X 0)) :
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * tOf f B a₀ a =
      embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) := by
  unfold tOf
  rw [mul_assoc, mul_inv_cancel_left]

theorem tOf_eq_iff (a₀ a : GA D (D.sp.X 0)) (t : GA D (D.sp.Y 0)) :
    tOf f B a₀ a = t ↔ embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) =
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * t := by
  rw [← shift_tOf, mul_right_inj]

end GlobalTheory.MiTop

end
