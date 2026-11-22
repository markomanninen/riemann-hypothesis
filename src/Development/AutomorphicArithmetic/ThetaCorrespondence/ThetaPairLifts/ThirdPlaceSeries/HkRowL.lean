module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem hecke_expansion_heightData_of_levelC {x : St P}
    (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) :
    NExpHeckeRowX x.m.z.R x.m.z.cG l.rat.S l.b.YS
      (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l) fun _ => LinearMap.id :=
  hkRow_of_ad x.m.z.R x.m.z.cG l.rat.kKs l.rat.hk l.b.YS
    (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l) l.rat.In.Sb l.b.fi l.b.Sb_le l.rat.rat.hecke

theorem hecke_expansion_datL_of_levelC {x : St P} (L : LocAll (lay0 (Dof x)))
    (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) :
    NExpHeckeRowX (datL x L).R (datL x L).cG (SL L l.rat)
      (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l)
      (_root_.GlobalTheory.HeightCounting.Fin3.localHeckeHeightData L l) fun _ => LinearMap.id := by
  constructor
  intro i k Q hsplit hoff houtside htwo hk α R hα hR y hy
  with_unfolding_all
    exact (hecke_expansion_heightData_of_levelC l).tie
      i k Q hsplit hoff houtside htwo hk α R hα hR y hy
end GlobalTheory.HeightCounting.Fin3
end
end
