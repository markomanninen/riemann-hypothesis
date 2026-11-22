module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
public import Formalism.LocalToGlobal.GroupLattices.TiedRec
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

section Ext

variable {Os Ks O Kf O' Kf' : Type} [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf']
  [Algebra O' Kf']

end Ext

section Ties

abbrev RingTie := @Formalism.L2.G.RingCompatibleAt

abbrev LocalIs := @Formalism.L2.G.GatIs

alias standardSub_of_ringTie := Formalism.L2.G.stdSubAt_of_ring

alias localIs_of_hyperspecial := Formalism.L2.G.gatIs_recG

alias ringTie_record := Formalism.L2.G.ringTied_recC

end Ties

section Bridge

theorem pack_eq (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ nFr D (D.what₂.places.resChar w))
    (he : Even (nFr D (D.what₂.places.resChar w)))
    (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ) :
    pack D u Lc w h5 h2 he I ψ = locPackC D u Lc w h5 h2 he I ψ := by
  first
    | with_reducible rfl
    | (delta pack locPackC frobOrder nFr; with_reducible rfl)

end Bridge

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

end Record

abbrev IsConcrete := @Formalism.L2.G.IsRecC

end GlobalTheory.Mem.LocalPack
