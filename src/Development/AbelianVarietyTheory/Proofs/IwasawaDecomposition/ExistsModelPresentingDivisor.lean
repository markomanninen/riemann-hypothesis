module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.LineNorm

section Closure

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

omit [NumberField F] in
theorem isEqn_sum {α : Type} (s : Finset α) {Δ : α → Y.Dv} {t : α → Y.Fnˣ} (y : Y.X)
    (h : ∀ a, (Δ a).IsEqn y (t a)) : (∑ a ∈ s, Δ a).IsEqn y (∏ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a).add ih

end Closure

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {F : Type} [Field F] [NumberField F] {Y : Var F}


open Classical in
def mixLog (ρ : Y.X ⟶ X) {m : ℕ}
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (b : ℕ → Bool) (i : Fin m) : PtFn Y :=
  fun v ε y =>
    if hp : (resP v).Prime then
      haveI := Fact.mk hp
      let ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ)
          (lat t (resP v) (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ) (b (resP v)))
          (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) i)
    else 0

end Steps

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

abbrev fr (y : C.Y.X) := (C.gr_spec y).choose_spec.choose

abbrev dg (y : C.Y.X) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ := (C.gr_spec y).choose_spec.choose_spec.choose

omit [NumberField F] in
theorem fr_spec (y : C.Y.X) : (fr C y).Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (dg C y) ∧
    ∀ τ i, (C.gr τ i).IsEqn y (dg C y τ i) := (C.gr_spec y).choose_spec.choose_spec.choose_spec





open Classical in
def symLog (b : ℕ → Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : PtFn C.Y := fun v ε y =>
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ (C.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v) (b (resP v)) st
  else 0


open Classical in
def lgCopy (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) : ℝ :=
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let f := (C.gr_spec (below y.1)).choose_spec.choose
    let t := (C.gr_spec (below y.1)).choose_spec.choose_spec.choose
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2
  else 0

theorem lgOf_eq_lgCopy : @lgOf = @lgCopy := rfl

theorem mul_finsupp_sum {α : Type} (w : α →₀ ℤ) (c : ℝ) (g : α → ℝ) :
    c * w.sum (fun a n => (n : ℝ) * g a) = ∑ a ∈ w.support, (w a : ℝ) * (c * g a) := by
  simp only [Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _

theorem lgCopy_eq (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) :
    lgCopy C w v ε y = Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, dg C (below y.1) x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      ∑ a ∈ w.support, (w a : ℝ) * symLog C a.1 a.2.2 v ε y := by
  obtain ⟨hp, -⟩ := GlobalTheory.ShFam.Pad.ioOf_spec F v ε
  simp only [lgCopy, symLog, dif_pos hp]
  refine congrArg₂ (fun a b : ℝ => a + b) rfl ?_
  refine (mul_finsupp_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine congrArg _ (congrArg _ ?_)
  rfl


end Flags

end GlobalTheory.LineNorm
