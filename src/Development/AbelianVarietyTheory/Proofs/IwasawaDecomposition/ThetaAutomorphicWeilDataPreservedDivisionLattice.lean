module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Top.Bl.ThTTr

open Formalism.L2.Theta Formalism.L2.JoinChr
open scoped TensorProduct
open Formalism.BasicNotions.TH (tauE)

section

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt)
  (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

abbrev thTrZ (X : ThetaX (w.D Z)) : ThetaX (w.D (setDivZ Z N h)) := { X with }

theorem isAutFun_tr {V : TH.HSp (w.D Z)} {φ : GA (w.D Z) V → ℂ} :
    IsAutFun (D := w.D Z) V φ ↔ IsAutFun (D := w.D (setDivZ Z N h)) V φ :=
  ⟨fun x => ⟨x.left, x.level, x.cont⟩, fun x => ⟨x.left, x.level, x.cont⟩⟩

theorem isAutFunSm_tr {θ : (w.D Z).what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf (w.D Z).host.F ⊗[(w.D Z).host.F] (w.D Z).host.E →+* ℂ)} {V : TH.HSp (w.D Z)}
    {φ : GA (w.D Z) V → ℂ} : IsAutFunSm (D := w.D Z) θ V φ ↔ IsAutFunSm (D := w.D (setDivZ Z N h)) θ V φ :=
  ⟨fun x => ⟨(isAutFun_tr w Z N h).1 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩,
   fun x => ⟨(isAutFun_tr w Z N h).2 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩⟩

theorem isThetaFun_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF (w.D Z).host.F) ℂ} {V W : TH.HSp (w.D Z)} {f : WA V W → ℂ} :
    IsThetaFun (D := w.D Z) ψ V W f ↔ IsThetaFun (D := w.D (setDivZ Z N h)) ψ V W f :=
  ⟨fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩, fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩⟩

theorem isPolFock_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF (w.D Z).host.F) ℂ}
    {θ : (w.D Z).what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf (w.D Z).host.F ⊗[(w.D Z).host.F] (w.D Z).host.E →+* ℂ)} {V W : TH.HSp (w.D Z)}
    {A : ∀ τ : (w.D Z).what₂.Tau, Matrix (Fin (V.sig (tauE (w.D Z) τ)).1 ⊕ Fin (V.sig (tauE (w.D Z) τ)).2) (Fin V.rank) ℂ}
    {B : ∀ τ : (w.D Z).what₂.Tau, Matrix (Fin (W.sig (tauE (w.D Z) τ)).1 ⊕ Fin (W.sig (tauE (w.D Z) τ)).2) (Fin W.rank) ℂ}
    {f : WA V W → ℂ} :
    IsPolFock (D := w.D Z) ψ θ V W A B f ↔ IsPolFock (D := w.D (setDivZ Z N h)) ψ θ V W A B f :=
  ⟨fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩,
   fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩⟩

@[reducible] def besDatTr {A B : TH.HSp (w.D Z)} {ι : A.V →ₗ[(w.D Z).host.E] B.V} (d : BesDat (D := w.D Z) A B ι) :
    BesDat (D := w.D (setDivZ Z N h)) A B ι := { d with }


set_option maxHeartbeats 4000000 in
def thetaTiedTr {X : ThetaX (w.D Z)} (T : ThetaTied (w.D Z) X) : ThetaTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) :=
  { T with ev_aut := fun V F => (isAutFun_tr w Z N h).1 (T.ev_aut V F) }


set_option maxHeartbeats 4000000 in
def weilTiedTr {X : ThetaX (w.D Z)} {T : ThetaTied (w.D Z) X} (Wl : WeilTied (w.D Z) X T) :
    WeilTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) (thetaTiedTr w Z N h T) :=
  { Wl with
    evS_range := fun V W hne => (Wl.evS_range V W hne).trans (Set.ext fun _ => isThetaFun_tr w Z N h)
    om_tw := { Wl.om_tw with } }


set_option maxHeartbeats 4000000 in
theorem weilTiedEq_tr {X : ThetaX (w.D Z)} {T : ThetaTied (w.D Z) X} {Wl : WeilTied (w.D Z) X T} (e : WeilCompatibleEquivariance Wl) :
    WeilCompatibleEquivariance (weilTiedTr w Z N h Wl) :=
  { e with
    evS_range := fun V W hr => (e.evS_range V W hr).trans (Set.ext fun _ => isThetaFun_tr w Z N h)
    om_tw := { e.om_tw with } }


set_option maxHeartbeats 4000000 in
def allTiedTr {X : ThetaX (w.D Z)} {A : TH.ProvA} (a : AllTied (w.D Z) X A) : AllTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) A where
  T := thetaTiedTr w Z N h a.T
  sm := ⟨a.sm.1, fun θ hθ V hV => (a.sm.2 θ hθ V hV).trans (Set.ext fun _ => isAutFunSm_tr w Z N h)⟩
  ty := { a.ty with }
  W := weilTiedTr w Z N h a.W
  unr := a.unr
  kf := { a.kf with
    kfin := ⟨a.kf.kfin.1, fun θ hθ V W h1 h2 h3 Φ => (a.kf.kfin.2 θ hθ V W h1 h2 h3 Φ).trans (isPolFock_tr w Z N h)⟩ }
  phiUp := a.phiUp
  B := { a.B with dat := fun A B ι ho p => besDatTr w Z N h (a.B.dat A B ι ho p) }
  real := { a.real with }
  prov := { a.prov with }


end

set_option maxHeartbeats 16000000 in
theorem thT_setDiv {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)}
    (n : NchT w Z Wt nch) (th : ThetaX (w.D Z))
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    ThT n th →
      let moved : NchT w (setDivZ Z N h) Wt { nch with } :=
        { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }
      Nonempty (ThT moved (thTrZ w Z N h th)) := by
  intro t
  exact ⟨{ provA := t.provA
           all := allTiedTr w Z N h t.all
           weq := weilTiedEq_tr w Z N h t.weq
           chr := { t.chr with }
           same := { t.same with }
           std := t.std
           io := t.io }⟩

end GlobalTheory.Mem.Top.Bl.ThTTr
