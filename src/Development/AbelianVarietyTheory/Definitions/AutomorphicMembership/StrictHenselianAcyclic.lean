module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev Dof (x : St P) : D7 := (w.st x.o.Z).toD7

abbrev cfOf (x : St P) : CharFrame (Dof x) := TC.cf w.I w.l x.o.Z


open Classical in
def QOf (P : Pre2 K w) (v : B.places.Pl) : Finset (HeightOneSpectrum (𝓞 B.host.E)) := if v ∈ P.Wt then T.Q v else ∅

structure LA (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 where
  a : StA hL (Dof x) (cfOf x) (repOf x.r.Y)
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (Dof x).host.E)) → PlE (Dof x).host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  sel : Set.range Pq = Set.range w.I.sel

structure LI (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LA hL x where
  mt : InMt x.r.Y (cfOf x) w.I.xi (QOf P)
  rat : InRat x.r.Y x.m.z.cG
  cusp : RowCusp (Dof x) a.A.row

structure SeriesLevel (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : SeriesState x.m.z.geo a rat mt.ad.PV Pq

structure StrictHenselianAcyclic (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : ModuliPointsState x.m.z.geo a rat mt.ad.PV Pq

structure LC (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends StrictHenselianAcyclic hL x where
  c : StC mt b T.k T.psi

abbrev AllSt (p : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop) : Prop :=
  StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), p K B f T w P x

variable (hL)

def SMt : Prop := AllSt fun _ _ _ _ w P x => Nonempty (InMt x.r.Y (cfOf x) w.I.xi (QOf P))

structure Kept {D D' : D7} (c : NChoice D) (c' : NChoice D') : Prop where
  gal : GlobalTheory.TwistChoice.SameGalois D.nd D'.nd
  set : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  forms : GlobalTheory.TwistChoice.SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  twI : HEq c.twI c'.twI
  sd : HEq c.sd c'.sd
  Q : HEq c.Q c'.Q
  k : HEq c.k' c'.k'
  psi : HEq c.psi' c'.psi'

end GlobalTheory.HeightCounting.Up

end
