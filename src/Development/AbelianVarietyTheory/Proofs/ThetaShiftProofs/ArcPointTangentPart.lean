module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.Frames.ChgBC

noncomputable section

namespace GlobalTheory.ArcQ.TanPart

section Mul

variable {B B' Z Z' : Scheme.{0}} {G : Over B} [GrpObj G] {G' : Over B'} [GrpObj G'] {f : B' ⟶ B}
  {φ : G'.left ⟶ G.left}

end Mul

section Eps

variable {S : Type} [CommRing S]

theorem fst_alg : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

end Eps

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S]

end Comb

section Gt

open GlobalTheory.TorusModel

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem isZero_of_isAdd {T : Over (Spec (CommRingCat.of A))} {g : Out.GtPt D₀ T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (GlobalTheory.TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := by
    exact (mul_eq_left.1 hb.symm)
  refine ⟨hb1, fun χ => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have face (x x' : T ⟶ D₀.P.A) : cubV D₀.cub y J 1 x x' = 1 := by
    have q := val_corr hJ (D₀.cub.face 0) (lift x x').left
    rw [val_one] at q
    refine (Eq.trans ?_ (val_cub D₀.cub (lift x x') hJ (pzero D₀.P.A _) (x2 D₀.P.A 0) (x2 D₀.P.A 1)).symm).trans q
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have swap01 (x x' w : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' w = cubV D₀.cub y J x' x w := by
    have q := (val_corr hJ D₀.cub.cubeSymmetric_swap_first (lift x (lift x' w)).left).trans (val_cub D₀.cub (lift x (lift x' w)) hJ _ _ _)
    refine q.trans ?_
    congr 1 <;> simp [x3]
  have swap12 (x x' w : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' w = cubV D₀.cub y J x w x' := by
    have q := (val_corr hJ D₀.cub.cubeSymmetric_swap_last (lift x (lift x' w)).left).trans (val_cub D₀.cub (lift x (lift x' w)) hJ _ _ _)
    refine q.trans ?_
    congr 1 <;> simp [x3]
  have face3 (x x' : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' 1 = 1 :=
    (swap12 _ _ _).trans ((swap01 _ _ _).trans (face _ _))
  rw [hb1] at e
  change cv g χ y J * cubV D₀.cub y J (DVR.cP D₀ T χ) 1 1 = _ at e
  rw [face3, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

end Gt

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

end ThetaShiftProofs

end GlobalTheory.ArcQ.TanPart
