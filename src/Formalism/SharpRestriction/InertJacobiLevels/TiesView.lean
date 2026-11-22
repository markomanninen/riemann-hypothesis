module

public import Formalism.SharpRestriction.InertJacobiLevels.TiesCore
public import Formalism.SharpRestriction.InertJacobiLevels.VVEqEmptyOfNotIsResidueClassZero
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def viewD (D : D7) : GC.GD := ⟨D.R, ⟨D.host.TT, D.host.T2, D.host.u0, D.host.cls⟩, G.hP D⟩

def viewL {D : D7} (L : SizeData₂ D) : GC.GParameters (viewD D) := ⟨L.sc, L.Sc, L.etaSz⟩

def viewX {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : GC.Inst (viewD D) (viewL L) where
  bs := X.bs
  bs_orb := X.bs_orb
  bs_step := X.bs_step
  off := X.off
  off_top := X.off_top
  off_thin := X.off_thin
  off_thick := X.off_thick
  kapI := X.kapI
  ep := X.ep

section View

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ)

end View

structure GAll where
  D : GC.GD
  L : GC.GParameters D
  X : GC.Inst D L
  a : GC.HH D → ℤ
  b : GC.HH D → ℤ

namespace GAll

variable (A : GAll) (K : G.Consts)



end GAll

def allOf {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : GAll := ⟨viewD D, viewL L, viewX X, G.aL L, G.bL L⟩

theorem host_cls_eq {R R' : Ranks} {H : Host R} {H' : Host R'} (hq : H.q = H'.q) (hd : H.d = H'.d)
    (hQS : H.QS = H'.QS) : H.cls = H'.cls := by
  have hN : H.toHostRaw.condN = H'.toHostRaw.condN := by
    simp only [Formalism.HC.HostRaw.condN, hq, hd, hQS]

  have hps : ∀ p, H.toHostRaw.psAt p = H'.toHostRaw.psAt p := by
    intro p
    unfold Formalism.HC.HostRaw.psAt
    by_cases hc : Nat.Coprime p H.toHostRaw.condN
    · have hc' : Nat.Coprime p H'.toHostRaw.condN := by
        rw [← hN]
        exact hc
      rw [dite_eq_left hc, dite_eq_left hc']
      have e := H.flPS (ZMod.unitOfCoprime p hc)
      have e' := H'.flPS (ZMod.unitOfCoprime p hc')
      rw [e, e']
      simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Formalism.HC.HostRaw.condN, hq, hd, hQS]
    · have hc' : ¬ Nat.Coprime p H'.toHostRaw.condN := by
        rw [← hN]
        exact hc
      rw [dite_eq_right hc, dite_eq_right hc']
  funext p
  unfold Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass
  rw [hps p]
  simp only [Formalism.HC.HostRaw.small, hq, hd, hQS]
  split_ifs <;> simp_all

section Tied

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts) (dr : Set ℕ)
  (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
  (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
  (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)


end Tied

end Formalism.MainNotions.Inhab

end
