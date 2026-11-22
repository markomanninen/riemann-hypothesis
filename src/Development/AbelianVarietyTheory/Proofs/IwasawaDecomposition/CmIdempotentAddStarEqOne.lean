module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.ArcBuild

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : P.D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ P.D χ).choose

theorem isQ_qv : QForm.IsQ P.D.toPre ϖ (qv P hϖ) := fun χ => (QForm.exists_QVal hϖ P.D χ).choose_spec

def beF : LinearMap.BilinForm ℤ P.D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D (isQ_qv P hϖ) a b)
    (fun a a' b => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : P.D.toPre.X) : beF P hϖ a b = beF P hϖ b a := QForm.bOf_comm P.D a b

theorem beF_self (a : P.D.toPre.X) : beF P hϖ a a = 2 * qv P hϖ a :=
  (QForm.two_Q_eq hϖ P.D (isQ_qv P hϖ) a).symm

theorem beF_adj (x : 𝓞 E) (a b : P.D.toPre.X) : beF P hϖ (x • a) b = beF P hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ P.D GlobalTheory.abelianSchemeLaws_all.1 P.oD (isQ_qv P hϖ) x a b

theorem beF_w0 (a : P.D.toPre.X) : beF P hϖ a (H.w0 • a) = qv P hϖ a := by
  have h₁ := beF_adj P hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm P hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self P hϖ a
  omega

def piK : (FractionRing T.V)ˣ :=
  Units.mk0 (algebraMap T.V (FractionRing T.V) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)

def tF (a b : P.D.toPre.X) : (FractionRing T.V)ˣ := piK hϖ ^ (-(beF P hϖ a b))

theorem cmIdempotent_add_star_eq_one : letI := H.starRing; H.w0 + star H.w0 = 1 := halfUnit_add_star H

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist P.D.toPre H.w0 (tF P hϖ)

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (m : SABMap t Y.t y)



end ThetaShiftProofs

end GlobalTheory.ArcBuild
