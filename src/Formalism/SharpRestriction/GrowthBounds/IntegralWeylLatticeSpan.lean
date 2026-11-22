module

public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieFin
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.BlockRationalityField
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BlockRatReal

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.L2.G.Cmp Formalism.L2.Herm

namespace Formalism.L2.G.RelativeIndexFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

theorem blockRationality_holds : Formalism.L2.G.BlockRationalityField := by
  intro p O Kf _ _ _ _ _ P Tau _ n LL _ h pos G M embLL lam hW hM
  exact blockRatReal P.lam0 h pos G M embLL (fun τ => (lam τ).w) (fun τ => (lam τ).anti) hW hM

section Rec

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

end Rec

variable (D : D7) (H : FullTiedNoG D)
  (I0 : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (H.base.lev0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB D B)
  (sc : Scale) (Ce : ℝ) (T : ∀ u : D.what₂.Word, Forms0 D u)
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (H.base.lev0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

variable {D H I0 B hBs sc Ce T ψ hd}

end Formalism.L2.G.RelativeIndexFlags
