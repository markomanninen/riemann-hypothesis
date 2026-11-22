module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReTo0S

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

open GlobalTheory.Mem.Db

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)


set_option maxHeartbeats 8000000 in
def nchTTr {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) :
    NchT w (setDivZ Z N h) Wt { nch with } :=
  { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }


set_option maxHeartbeats 8000000 in
def kerTr {Gt : GatTies (w.D Z)} {cmp : LatCmp (w.D Z)} {Gy : G.LatInst (w.D Z)} (k : KerFam (w.D Z) Gt cmp (w.tw Z) Gy) :
    KerFam (w.D (setDivZ Z N h)) { Gt with } { cmp with } (w.tw (setDivZ Z N h)) { Gy with } :=
  fun u v g => { k u v g with }


set_option maxHeartbeats 8000000 in
def columnLocalDataTransportDivision (c : ColumnDataSplitPrimes K w Z)
    (hR : let t := DivTr.colTTr w Z N h c.toColT
          IsRecG K.s (w.D (setDivZ Z N h)) t.Gt t.cmp t.g.herm t.g.forms) :
    ColumnDataSplitPrimes K w (setDivZ Z N h) :=
  { DivTr.colTTr w Z N h c.toColT with isRec := hR, om := c.om }

end GlobalTheory.Mem.Top.Bl.WitTr

end
