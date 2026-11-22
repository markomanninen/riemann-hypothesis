module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}


open Classical in
def givenFn (B : Frames G) (t : T) (Φ : G.Datum) (e : AE D) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) : ℂ :=
  if IsHalf e x then ∏ w ∈ locPl G t, givenDatum t w B Φ (edgeOf a) (locArg B t w a x) else 0

end GlobalTheory.FlipStart

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem tensor_given (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E)
    (y : ∀ j : Fin D.R.m, WO (G.pS (Arrow.down t 0 j).pair) (G.pT (Arrow.down t 0 j).pair))
    (x : ∀ i : Fin D.R.m, WO (G.pS (Arrow.right (T := T) i 0).pair) (G.pT (Arrow.right (T := T) i 0).pair)) :
    (givenStage t w B Φ).tensor (pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x))) =
      (∏ j : Fin D.R.m, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) (y j))) *
        ∏ i : Fin D.R.m, givenDatum t w B Φ (edgeOf (.right i 0)) (locArg B t w (.right i 0) (x i)) := by
  have pathArgs_down (i : ℕ) : ∀ (n : ℕ) (y : ∀ j : Fin n, WO (G.pS (Arrow.down t i j).pair) (G.pT (Arrow.down t i j).pair))
      (j : ℕ) (h : j < n), pathArgs B t w (downPath t i n) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n y) (.theta i j) =
        locArg B t w (.down t i j) (y ⟨j, h⟩) := by
    intro n
    induction n with
    | zero => intro y j h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro y j h
      have hc := GlobalTheory.OppConv.pathArgs_comp B t w (Path.one (.down t i n)) ((), y (Fin.last n)) (.theta i j) (downPath t i n)
        (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n fun j => y j.castSucc)
      by_cases hj : j < n
      · exact (hc.1 ((GlobalTheory.OppConv.mem_edges_down t i n _).2 ⟨j, hj, rfl⟩)).trans (ih _ j hj)
      · have hj' : j = n := by omega
        subst hj'
        refine (hc.2 fun h' => ?_).trans ?_
        · obtain ⟨k, hk, hk'⟩ := (GlobalTheory.OppConv.mem_edges_down t i j _).1 h'
          simp only [GlobalTheory.SplitFlip.Edge.theta.injEq] at hk'
          omega
        · exact dif_pos rfl
  have hθ : ∀ j : Fin D.R.m, pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x)) (.theta 0 j) = locArg B t w (.down t 0 j) (y j) := by
    intro j
    refine ((GlobalTheory.OppConv.pathArgs_comp B t w (downPath t 0 D.R.m) _ (.theta 0 j) (rowPath T 0 D.R.m) _).2 ?_).trans
      (pathArgs_down 0 D.R.m y j j.2)
    rw [GlobalTheory.OppConv.mem_edges_row]
    rintro ⟨i, -, h⟩
    cases h
  have hex : ∀ i : Fin D.R.m, pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x)) (.ex i 0) = locArg B t w (.right i 0) (x i) :=
    fun i => ((GlobalTheory.OppConv.pathArgs_comp B t w (downPath t 0 D.R.m) _ (.ex i 0) (rowPath T 0 D.R.m) _).1
      ((GlobalTheory.OppConv.mem_edges_row 0 D.R.m _).2 ⟨i, i.2, rfl⟩)).trans (GlobalTheory.OppConv.pathArgs_row B t w 0 D.R.m x i i.2)
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b _).prod = _
  simp only [GlobalTheory.SplitFlip.givenPath, List.map_append, List.prod_append, List.map_map, List.map_reverse, List.prod_reverse]
  have hl : ∀ f : ℕ → ℂ, ((List.range D.R.m).map f).prod = ∏ i : Fin D.R.m, f i := fun f => by
    rw [← Finset.prod_range, Finset.prod_eq_multiset_prod]; rfl
  rw [hl, hl]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    rw [hθ j]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    rw [hex i]
    rfl

end GlobalTheory.FlipStart

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem repFin_of (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j))
    (Φ : G.Datum) (e : AE D) (he : IsIdemSum e (locPl G t)) (c : Fin D.R.m → ℂ) (z : ℂ) (hz : z * ∏ j, c j = 1)
    (hcol : ∀ j : Fin D.R.m, IsLocVec W (.mu t 0 j) e (ρ.vT 0 j) (c j • givenFn B t Φ e (.down t 0 j)) (f j))
    (hrow : ∀ i : Fin D.R.m, IsLocVec W (.chi i 0) e (ρ.vX i 0) (givenFn B t Φ e (.right i 0)) (W.cosVec i (Φ i))) :
    RepFin B ρ t (givenPath t D.R.m) (Finsupp.single (givenFin W t f Φ) z) (fun w => (givenStage t w B Φ).tensor) := by
  have append_surj {S : Arrow T → Type} {X Y : Node} (p : Path T X Y) :
      ∀ {Z : Node} (q : Path T Y Z) (f : (p.comp q).Fam S), ∃ d e, Path.Fam.append (q := q) d e = f := by
    intro Z q
    induction q with
    | nil => intro f; exact ⟨f, (), rfl⟩
    | snoc a q ih =>
      intro f
      obtain ⟨d, e, h⟩ := ih f.1
      refine ⟨d, (e, f.2), ?_⟩
      show (Path.Fam.append (q := q) d e, f.2) = f
      rw [h]
      rfl
  have rowFam_surj {S : Arrow T → Type} (j : ℕ) : ∀ n (d : (rowPath T j n).Fam S), ∃ f, rowFam j n f = d := by
    intro n
    induction n with
    | zero => intro d; exact ⟨fun i => i.elim0, rfl⟩
    | succ n ih =>
      intro d
      obtain ⟨f, hf⟩ := ih d.1
      refine ⟨Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f, ?_⟩
      show (rowFam j n (fun i => Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f i.castSucc),
        Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f (Fin.last n)) = d
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl
  have downFam_surj {S : Arrow T → Type} (i : ℕ) : ∀ n (d : (downPath t i n).Fam S), ∃ f, downFam t i n f = d := by
    intro n
    induction n with
    | zero => intro d; exact ⟨fun j => j.elim0, rfl⟩
    | succ n ih =>
      intro d
      obtain ⟨d0, e, he⟩ := append_surj (Path.one (.down t i n)) (downPath t i n) d
      obtain ⟨f, hf⟩ := ih e
      refine ⟨Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f, ?_⟩
      rw [← he]
      show Path.Fam.append (p := Path.one (.down t i n)) ((), Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f (Fin.last n))
        (downFam t i n fun j => Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f j.castSucc) = _
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl
  refine ⟨e, he, fun _ => Path.Fam.append (q := rowPath T 0 D.R.m)
    (downFam t 0 D.R.m fun j => c j • givenFn B t Φ e (.down t 0 j)) (rowFam 0 D.R.m fun i => givenFn B t Φ e (.right i 0)),
    fun d hd => ?_, fun x hx => ?_⟩
  · rw [Finsupp.support_single_ne_zero _ (by rintro rfl; simp at hz), Finset.mem_singleton] at hd
    subst hd
    exact (GlobalTheory.OppConv.vecAll_append ρ e _ _ _ _ _ _).2
      ⟨(GlobalTheory.OppConv.vecAll_down ρ e t 0 _ _ _).2 hcol, (GlobalTheory.OppConv.vecAll_row ρ e 0 _ _ _).2 hrow⟩
  · rw [Finsupp.sum_single_index (by rw [zero_mul])]
    obtain ⟨x₁, x₂, rfl⟩ := append_surj (downPath t 0 D.R.m) (rowPath T 0 D.R.m) x
    obtain ⟨y, rfl⟩ := downFam_surj 0 D.R.m x₁
    obtain ⟨y', rfl⟩ := rowFam_surj 0 D.R.m x₂
    obtain ⟨h1, h2⟩ := (GlobalTheory.OppConv.halfAll_append e _ _ _ _).1 hx
    have hy := (GlobalTheory.OppConv.halfAll_down e t 0 _ _).1 h1
    have hy' := (GlobalTheory.OppConv.halfAll_row e 0 _ _).1 h2
    dsimp only
    rw [Finset.prod_congr rfl fun w _ => tensor_given B t Φ w y y']
    erw [GlobalTheory.OppConv.famProd_append (downPath t 0 D.R.m), GlobalTheory.OppConv.famProd_down, GlobalTheory.OppConv.famProd_row]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, givenFn, if_pos (hy _), if_pos (hy' _)]
    rw [Finset.prod_comm (s := Finset.univ) (t := locPl G t), Finset.prod_comm (s := Finset.univ) (t := locPl G t),
      ← mul_assoc, ← mul_assoc, hz, one_mul]

end GlobalTheory.FlipStart

end
