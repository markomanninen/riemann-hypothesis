module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabels
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtildeCSD t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF D.sp.X') (R.B.R t).pres op inR (fun i => IsLabElt D.sp.X' (pl i) (ty i)) (fun i => IsLocElt D.sp.X' (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtildeCSD t).Forms, (A.MtildeCSD t).csum ((op i f : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) (g : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) = (A.MtildeCSD t).csum (f : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) ((op i g : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V)) ∧ IsLab D.sp.X' (pl i) (ty i) ∧ ∀ h, IsOpsX R t h → ∀ f, R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM t I pl ty op inR hin HT i hi
  obtain ⟨hgood, hconj, hpw⟩ := hin i hi
  have hd := GlobalTheory.InertRows.ext_op_eq D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX
    R.cX.coef.ρ D.what₂.embLL (A.MtildeCSD t) (R.B.R t).pres pl ty op inR HT i hi hgood hpw
  have hint : ∀ h, IsOpsX R t h → ∀ f,
      R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
    intro h hh f
    refine (hM.HX t).1 ((hM.jX t _).trans ((hd.2 f).trans ?_))
    exact (congrArg (hkF D.sp.X' (pl i) (Finsupp.single (ty i) 1)) (hM.jX t f).symm).trans
      (hh (pl i) hgood _ _).symm
  refine ⟨?_, ?_, hd.1, hint⟩
  · obtain ⟨_, _, _, hT⟩ := hF.tie
    open GlobalTheory.HeckeRational in
    exact (dcOp_matrix_mem_cmMax D.sp.X' R.cX.coef R.βX (R.datXt t) (R.B.R t).pres
      (hT.coefR t) hT.mapR
      (fun g a b => (GlobalTheory.coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g a b).1)
      (HT.hA i) (op i) (HT.op_eq i hi)).2
  · intro f g
    obtain ⟨h, hh, hnormal⟩ := GlobalTheory.DefiniteOps.side D.sp.X' R.βX R.ΛX (R.datXt t)
      hL.βX (Good R t) (fun _ hp => hp) R.cX.coef.ρ (fun γ => hM.cX.2.1 γ)
      (R.B.R t).pres.y (R.B.R t).pres.reps
      (fun c => Finite.of_equiv _ ((R.B.R t).pres.stabI c).toEquiv) (R.HX t) (hM.HX t)
    have hdual : dualLab (ty i) = ty i :=
      ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing D.sp.X' (pl i) (ty i)).1 hd.1).2.2 hconj
    have hadj := (hnormal.2 (pl i) hgood (Finsupp.single (ty i) 1)).trans
      (congrArg (h (pl i)) (GlobalTheory.InertRows.dualC_single hdual))
    exact GlobalTheory.InertRows.csum_selfAdj (Bridge.ratF D.sp.X') (A.MtildeCSD t)
      D.what₂.embLL R.cX.coef.ρ _ _ (R.B.R t).pres (R.HX t) (hM.HX t)
      (R.jX t) (hM.jX t) (op i) _ hadj (hint h hh) f g
