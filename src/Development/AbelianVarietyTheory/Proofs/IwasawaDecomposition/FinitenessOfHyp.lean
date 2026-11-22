module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalEigenData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalLevelData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalCharacterData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeVISupIndep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerMapRep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NTiedLocTiedOfBuilt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataStateLocalisationsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedReadingsRelatedLocalizedAdelicDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetupLGood
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricCharacterGridListKeptLocalizedStageStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelation

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : LC hL x)

theorem mtIn : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
  show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
  rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt

variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : AutSpec l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))

def ntW : NTrue hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
  { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row
    low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs
    M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := mtIn l, big := big, L := L, Sp := Sp, Au := Au, ss := ss
    eq := rfl, pack := rfl }


variable (L) in
structure AllL : Type 1 where
  a : NAllC (withLoc L) (chL L l.c.ch)
  chr : (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L l.c.ch)) = ⟨cfL L (cfOf x), tpL L l.c.tp⟩
  jE : a.gal.fr.jE = l.a.jE
  mt : a.gal.mt = mtL L l.mt.M
  exp : ExpRel L l.b.Bs.exp a.exp
  chrN : NCharTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  chrGal : NGalChrTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  loc : ∀ F : Formalism.L2.RowFrame (withLoc L), F.rep = repOf x.r.Y → Formalism.L2.RowLocTied (withLoc L) a.gal.lp F


theorem low_ok (D : D7) : 2 ∈ lowAll D ∧ AbsolutelyIrreducibleSpan.q0 D ∈ lowAll D ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ lowAll D ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := by
  refine ⟨by simp [lowAll, Formalism.L2.lowPr], by simp [lowAll, Formalism.L2.lowPr], fun p hp => ?_, fun p hp => ?_⟩ <;>
    simp only [lowAll, Formalism.L2.lowPr, Finset.mem_union, Finset.mem_insert] <;> tauto

variable (al : AllL l L) (hLg : GlobalTheory.CoefDuty.Large (withLoc L))

theorem pqW (i j b k Q ψ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (hadm : Formalism.L2.NX.AdmTw (withLoc L) i k Q ψ) :
    plsOf al.a.exp i j b k Q ψ h1 h2 hadm = (qpOf (Dof x) l.Pq Q, qpOf (Dof x) l.Pq ((Dof x).ntw.pD i)) :=
  (al.exp.pl i j b k Q ψ h1 h2 hadm).trans (Prod.ext (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).1 (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).2)

def natW : NAt hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) where
  nt := ntW l Sp Au ss
  all := al.a
  chr_eq := al.chr
  host := ⟨(by with_unfolding_all exact (l.a.host.fr :)), (by with_unfolding_all exact (l.a.host.jLL :)), (by with_unfolding_all exact (l.a.host.embLL :))⟩
  frameN := by
    intro y
    with_unfolding_all exact (RingHom.congr_fun al.jE y).trans (l.a.frame y)
  chrN := al.chrN
  chrGal := al.chrGal
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  pq := fun i j b k Q ψ h1 h2 hadm => ⟨(by with_unfolding_all exact ((congrArg Prod.fst (pqW l al i j b k Q ψ h1 h2 hadm)) :)),
    (by with_unfolding_all exact ((congrArg Prod.snd (pqW l al i j b k Q ψ h1 h2 hadm)) :))⟩
  jE_eq := (by with_unfolding_all exact ((heq_of_eq al.jE.symm) :))
  mt_eq := (by with_unfolding_all exact ((heq_of_eq al.mt.symm) :))
  Pq_eq := (by with_unfolding_all exact ((HEq.refl l.Pq) :))
  low := (by with_unfolding_all exact ((low_ok (Dof x)) :))
  split := hLg.2.1
  ratIn := l.rat.In
  ratIn_hL := rfl
  ratIn_eig := rfl
  ratIn_θ := rfl
  depth := l.a.depth

abbrev PackedNAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) :=
  Σ (cf : CharFrame D) (c : NChoice D) (tp : TupTied D cf c), NAt hL D cf c tp

-- Transport the character data and the record together so their indices stay aligned.
def natDData : PackedNAt hL (DL x L) :=
  Eq.rec (motive := fun D _ => PackedNAt hL D)
    ⟨cfL L (cfOf x), chL L l.c.ch, tpL L l.c.tp, natW l Sp Au ss al hLg⟩ (DL_eq x L).symm

abbrev natD := (natDData l Sp Au ss al hLg).2.2.2

theorem packedNAt_transport_heq {D D' : D7} (e : D = D') (a : PackedNAt hL D) :
    let b : PackedNAt hL D' := Eq.rec (motive := fun d _ => PackedNAt hL d) a e
    HEq (ratL b.2.2.2.nt.L b.2.2.2.nt.S) (ratL a.2.2.2.nt.L a.2.2.2.nt.S) ∧
      HEq b.2.2.2.nt.hL a.2.2.2.nt.hL ∧ HEq b.2.2.2.nt.rep a.2.2.2.nt.rep := by
  cases e
  exact ⟨HEq.refl _, HEq.refl _, HEq.refl _⟩

theorem natD_heq :
    HEq (ratL (natD l Sp Au ss al hLg).nt.L (natD l Sp Au ss al hLg).nt.S) (ratL L l.rat.S) ∧
      HEq (natD l Sp Au ss al hLg).nt.hL l.rat.In.hL ∧
      HEq (natD l Sp Au ss al hLg).nt.rep (repOf x.r.Y) :=
  packedNAt_transport_heq (DL_eq x L).symm
    ⟨cfL L (cfOf x), chL L l.c.ch, tpL L l.c.tp, natW l Sp Au ss al hLg⟩


include l in
variable (L) in
theorem grpD : Formalism.L2.DIV.GrpTie (DL x L) (famR (w.st (oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) (datL x L).Xg (datL x L).tr).A
    (datL x L).F.P0 (datL x L).F.ψ0 (datL x L).F.P1 (datL x L).F.ψ1 ((datL x L).R.eG.trans (datL x L).cG) :=
  ⟨(by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).card :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).e0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).lvl0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).psi0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).idxSharp :)),
    (datL x L).pins.keep.psi.lvl⟩

variable {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y)

def frameY : Formalism.L2.RowFrame (DL x L) := Formalism.L2.Col.rowFrameOf (DL x L) _ Y.eFT

def rowD : NRow (D := DL x L) (natD l Sp Au ss al hLg) (datL x L).R (datL x L).F (datL x L).cG Y where
  kKs := kKsL L l.rat
  hk := hkL L l.rat
  nexp := ysL L l
  hecke := hkHL L l
  grp := grpD l L
  rowLoc := by
    let F : Formalism.L2.RowFrame (withLoc L) :=
      ⟨(frameY Y).rep, (frameY Y).inj⟩
    have hF : F.rep = repOf x.r.Y := by
      with_unfolding_all exact eq_of_heq hY.rep
    exact ⟨by with_unfolding_all exact ((al.loc F hF).sat :)⟩
  S_eq := (natD_heq l Sp Au ss al hLg).1.trans (SL_heq L l.rat)
  hL_eq := by with_unfolding_all exact ((natD_heq l Sp Au ss al hLg).2.1 :)
  rep_eq := by with_unfolding_all exact ((natD_heq l Sp Au ss al hLg).2.2.trans hY.rep.symm :)



def RowsAt (P : Pre2 K w) : Prop := ∀ x : St P, (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) →
  ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW




end GlobalTheory.HeightCounting.Fin3

end
