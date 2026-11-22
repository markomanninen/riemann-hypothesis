module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
variable (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)

set_option maxHeartbeats 8000000 in
def yStructureLocal : NExpRealS (datL x L).R (datL x L).cG (SL L l.rat) := by
  let Y : NExpRealS (datL x L).R (datL x L).cG (ratL L l.rat.S) := {
    fi := by with_unfolding_all exact (l.b.YS.fi :)
    geq := by with_unfolding_all exact (l.b.YS.geq :)
    rho := by with_unfolding_all exact (l.b.YS.rho :)
    chi := by with_unfolding_all exact (l.b.YS.chi :)
    eF := by
      intro i j b h1 h2
      with_unfolding_all exact (l.b.YS.eF i j b h1 h2 :)
    bsup := by
      intro i j b h1 h2
      with_unfolding_all exact (l.b.YS.bsup i j b h1 h2 :)
    act := by
      intro i j b h1 h2 g y
      with_unfolding_all exact (l.b.YS.act i j b h1 h2 g y :) }
  with_unfolding_all exact (Y :)

def heckeHeightData : NExpRealH x.m.z.R x.m.z.cG l.rat.S l.b.YS where
  hL := l.rat.In.hL
  hs := l.b.Bs.hs
  cHk := fun i b k Q => algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) (l.b.Bs.cHk i b Q) ^ k
  cHk_zero := fun i b Q => pow_zero _
  cHk_unit := fun i b Q =>
    ((l.b.Bs.cHk i b Q).isUnit.map (algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)))).pow 1
  cHk_pow := fun i b k Q => by simp only [pow_one]
  hkEq := by rw [l.b.eF]; exact l.b.Bs.hkEq

def localHeckeHeightData : NExpRealH (datL x L).R (datL x L).cG (SL L l.rat) (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) := by
  let Y : NExpRealS (datL x L).R (datL x L).cG (ratL L l.rat.S) := by
    with_unfolding_all exact (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l :)
  let H : NExpRealH (datL x L).R (datL x L).cG (ratL L l.rat.S) Y := {
    hL := by with_unfolding_all exact ((heckeHeightData l).hL :)
    hs := by with_unfolding_all exact ((heckeHeightData l).hs :)
    cHk := by with_unfolding_all exact ((heckeHeightData l).cHk :)
    cHk_zero := by with_unfolding_all exact ((heckeHeightData l).cHk_zero :)
    cHk_unit := by with_unfolding_all exact ((heckeHeightData l).cHk_unit :)
    cHk_pow := by with_unfolding_all exact ((heckeHeightData l).cHk_pow :)
    hkEq := by
      intro i j b h1 h2 k Q y hQ hsplit hk
      with_unfolding_all exact ((heckeHeightData l).hkEq i j b h1 h2 k Q y hQ hsplit hk :) }
  with_unfolding_all exact (H :)

def psiVectorLocal : ∀ i : Fin (DL x L).R.m, principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (DL x L) i) (DL x L).R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oL x L).Z (l.mt.ad.PV ((i)))) : _))
def characterChoiceLocal : NChoice (DL x L) := { l.c.ch with }
def localCharacterTupleAgreement : TupTied (DL x L) (cfD x L) (characterChoiceLocal L l) :=
  { l.c.tp with }
def localMultiplicityFamily : MtFam (DL x L) := fun μ j h1 h2 =>
  { l.mt.M μ j h1 h2 with }
def placeMapLocal : HeightOneSpectrum (𝓞 (maximalRealSubfield (DL x L).host.E)) → PlE (DL x L).host := (by with_unfolding_all exact (l.Pq :))
def localEigenvalueDegree : ℕ → (DL x L).what₂.FT → ℕ → PlE (DL x L).host → ↥(DL x L).LL0 := (by with_unfolding_all exact (l.rat.In.eig :))
def smallPlaceSet : Finset (PlE (DL x L).host) := (by with_unfolding_all exact (l.rat.In.Sb :))
theorem twist_ok_local : ∀ v, TwistedAt (DL x L) v → IntegralHeckeForms.TwOK ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).twI v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).k' v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).Q v)
    (((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).psi' v).comp ((DL x L).ntw.art ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).twI v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).Q v))) := by
  intro v hv
  with_unfolding_all exact (l.c.ok v hv :)

set_option maxHeartbeats 8000000 in
theorem thetaTie_yStructureLocal_nonempty : Nonempty (GlobalTheory.GeoTie.ThetaTie (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.fw (DL x L).nth) := by
  let Y : NExpRealS (datL x L).R (datL x L).cG (ratL L l.rat.S) := by
    with_unfolding_all exact (yStructureLocal L l :)
  with_unfolding_all change Nonempty (GlobalTheory.GeoTie.ThetaTie Y (datL x L).geo.fw (DL x L).nth)
  obtain ⟨g⟩ := l.b.geo
  refine ⟨{ side := ?_, isUnramified₂ := ?_ }⟩
  · intro i j b
    let side := g.side (by with_unfolding_all exact (i :)) (by with_unfolding_all exact (j :)) b
    refine { pt := ?_, cover := ?_, ev_eq := ?_, fmUr := ?_, hk := ?_, hk_none := ?_ }
    · with_unfolding_all exact (side.pt :)
    · intro z
      with_unfolding_all exact (side.cover z :)
    · intro f y
      with_unfolding_all exact (side.ev_eq f y :)
    · intro f
      with_unfolding_all exact (side.fmUr f :)
    · intro k P hP
      with_unfolding_all exact (side.hk k P hP :)
    · intro k P hP y hy c
      with_unfolding_all exact (side.hk_none k P hP y hy c :)
  · intro i
    with_unfolding_all exact (g.isUnramified₂ i :)

theorem kept_characterChoiceLocal : Kept l.c.ch (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) :=
  ⟨sameGaloisL L, twistDataAgreeAcrossCoefficients_localized L, sameFormsL L, (by with_unfolding_all exact ((HEq.refl (Dof x).ntwbr) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.twI) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.sd) :)),
    (by with_unfolding_all exact ((HEq.refl l.c.ch.Q) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.k') :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.psi') :))⟩
theorem yStructureLocal_fi_e_heq : ∀ i y, HEq (((_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l).fi i).e y) y := (by with_unfolding_all exact (l.b.fi :))
end GlobalTheory.HeightCounting.Fin3
end
end
