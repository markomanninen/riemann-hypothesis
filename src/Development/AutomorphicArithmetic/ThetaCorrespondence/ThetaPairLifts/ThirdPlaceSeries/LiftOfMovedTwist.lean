module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDstA
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.Up.LiTw
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
section Gen
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}
private theorem charFrame_heq {D D' : D7} (hD : D = D')
    (a : CharFrame D) (b : CharFrame D')
    (hP : HEq a.P b.P) (hW : HEq a.W b.W) (hmu : HEq a.mu0 b.mu0)
    (heta : HEq a.eta b.eta) (hchi : HEq a.chiPsi b.chiPsi)
    (hdel : HEq a.del b.del) (hdel' : HEq a.del' b.del') : HEq a b := by
  subst D'
  cases a
  cases b
  cases eq_of_heq hP
  cases eq_of_heq hW
  cases eq_of_heq hmu
  cases eq_of_heq heta
  cases eq_of_heq hchi
  cases eq_of_heq hdel
  cases eq_of_heq hdel'
  rfl

private def reindexBase {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D D' : D7}
    {cf : CharFrame D} {cf' : CharFrame D'}
    {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    {rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r}
    (hD : D = D') (hcf : HEq cf cf') (hrep : HEq rep rep')
    (a : HeightCountingBaseData hL D cf rep) (ha : RowCusp D a.A.row) :
    {a' : HeightCountingBaseData hL D' cf' rep' // RowCusp D' a'.A.row ∧ HEq a'.A.row a.A.row} := by
  subst D'
  cases eq_of_heq hcf
  cases eq_of_heq hrep
  exact ⟨a, ha, HEq.rfl⟩

@[no_expose] def movedTwistBase {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
    (l : IntermediateLevel hL x) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh)
    (r : ReadPk m (sideTw x N)) (hp : r.Pin) (e : HEq (repOf r.Y) (repOf x.r.Y)) :
    {a : HeightCountingBaseData hL (Dof (stTw x N m hc hh r hp)) (cfOf (stTw x N m hc hh r hp))
        (repOf (stTw x N m hc hh r hp).r.Y) //
      RowCusp (Dof (stTw x N m hc hh r hp)) a.A.row ∧ HEq a.A.row (N.row l.a.A.row)} := by
  have hD : N.toD7 = Dof (stTw x N m hc hh r hp) := (dof_oTw x N).symm
  have hcf : HEq (N.cf (cfOf x)) (cfOf (stTw x N m hc hh r hp)) := by
    with_unfolding_all
      apply charFrame_heq hD <;> rfl
  let rep := repOf r.Y
  have hrep := HEq.refl rep
  let a := _root_.UpperTheory.One.M.stageAOfSwitch trivial N l.a
    (by with_unfolding_all exact rep) (by with_unfolding_all exact e)
  with_unfolding_all
    exact reindexBase hD hcf hrep a (cusp N l.cusp)

def liftOfMovedTwist {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) (e : HEq (repOf r.Y) (repOf x.r.Y)) (mt : InMt r.Y (cfOf (stTw x N m hc hh r hp)) w.I.xi (QOf P)) (rat : InRat r.Y m.z.cG) :
    _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp) where
  a := (movedTwistBase l m hc hh r hp e).val
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  sel := (by with_unfolding_all exact (l.sel :))
  mt := (by with_unfolding_all exact (mt :))
  rat := (by with_unfolding_all exact (rat :))
  cusp := (movedTwistBase l m hc hh r hp e).property.1
theorem li_copy_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  intro hL K B f T w P x l N m hm hc hh r hp e H1 H2
  cases m
  dsimp only at hm
  subst hm
  have G2 : ∀ i y, x.r.Y.mj.eW i y = eWB (N := N) ((by with_unfolding_all exact (r.Y :))) i y := fun i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H2 ((i)) ((y)))) : _)))
  have mt : InMt r.Y (cfOf (stTw x N _ hc hh r hp)) w.I.xi (QOf P) := by
    refine
      { M := fun μ j h1 h2 => by
          with_unfolding_all exact { l.mt.M μ j h1 h2 with }
        ad :=
          { PV := fun i =>
              { ψ := by with_unfolding_all exact (l.mt.ad.PV i).ψ
                inj := by with_unfolding_all exact (l.mt.ad.PV i).inj
                into := by with_unfolding_all exact (l.mt.ad.PV i).into
                onto := by with_unfolding_all exact (l.mt.ad.PV i).onto }
            std := by with_unfolding_all exact l.mt.ad.std
            eW := by with_unfolding_all exact l.mt.ad.eW
            read := fun μ h i y g => by
              have hRead := congrFun (eq_of_heq (H1 μ h i y)) ((l.mt.ad.PV i).ψ g)
              with_unfolding_all exact (l.mt.ad.read μ h i y g).trans hRead.symm
            rat := by with_unfolding_all exact l.mt.ad.rat
            wt := by with_unfolding_all exact l.mt.ad.wt
            id := by with_unfolding_all exact l.mt.ad.id }
        mt := ?_ }
    with_unfolding_all
      exact ⟨l.mt.mt.prod, l.mt.mt.para, l.mt.mt.uni, l.mt.mt.hyp,
        l.mt.mt.wt, l.mt.mt.rat, l.mt.mt.int, l.mt.mt.full⟩
  refine ⟨liftOfMovedTwist l _ hc hh r hp e mt ?_, ?_⟩
  · with_unfolding_all exact inRat (N := N) r.Y G2 l.rat
  · constructor
    · with_unfolding_all exact (movedTwistBase l _ hc hh r hp e).property.2
    · with_unfolding_all
        exact ⟨HEq.refl l.Pq, HEq.refl (N.rat l.rat.S), HEq.refl l.rat.In.Sb,
          HEq.refl l.rat.In.hL, HEq.refl l.rat.In.eig, HEq.refl l.rat.In.θ⟩
end GlobalTheory.HeightCounting.Up.LiTw
end
end
