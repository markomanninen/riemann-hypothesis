module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def Cell : Set (G1 F) := {g | IsUnit (g 1 0)}
theorem nmwn_val (b₁ b₂ : A F) (a : (A F)ˣ) : (nU b₁ * mD a * wW F * nU b₂).1 =
    !![-(b₁ * ((a⁻¹ : (A F)ˣ) : A F)), a - b₁ * ((a⁻¹ : (A F)ˣ) : A F) * b₂;
      -((a⁻¹ : (A F)ˣ) : A F), -(((a⁻¹ : (A F)ˣ) : A F) * b₂)] := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [nU] <;> ring
theorem nmwn_mem_cell (b₁ b₂ : A F) (a : (A F)ˣ) : nU b₁ * mD a * wW F * nU b₂ ∈ Cell F := by
  change IsUnit ((nU b₁ * mD a * wW F * nU b₂).1 1 0)
  rw [nmwn_val]; exact (a⁻¹).isUnit.neg

theorem cell_normal (g : G1 F) (c : (A F)ˣ) (hc : g 1 0 = c) :
    g = nU (g 0 0 * ((c⁻¹ : (A F)ˣ) : A F)) * mD (-c⁻¹) * wW F * nU (((c⁻¹ : (A F)ˣ) : A F) * g 1 1) := by
  have hd := specialLinear_det_entries g
  have hu := c.mul_inv
  rw [hc] at hd
  refine Subtype.ext ?_
  rw [nmwn_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hc]
  linear_combination (-((c⁻¹ : (A F)ˣ) : A F)) * hd - g 0 1 * hu
theorem mem_cell_iff (g : G1 F) : g ∈ Cell F ↔ ∃ b₁ a b₂, g = nU b₁ * mD a * wW F * nU b₂ :=
  ⟨fun h => ⟨_, _, _, cell_normal g (IsUnit.unit h) rfl⟩, by rintro ⟨b₁, a, b₂, rfl⟩; exact nmwn_mem_cell _ _ _⟩


variable (F) in
def p1 : A F →+* InfiniteAdeleRing F := RingHom.fst _ _

variable (F) in
def p2 : A F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

def pv (v : HeightOneSpectrum (𝓞 F)) : A F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F) v).comp (RingHom.snd _ _)
theorem adeleInfiniteComponent_apply (x : A F) : p1 F x = x.1 := rfl
theorem isUnit_adele_iff (x : A F) :
    IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧ ∀ᶠ v in cofinite, Valued.v (x.2 v) = 1 := by
  rw [← FiniteAdeleRing.isUnit_iff]
  refine Iff.trans (Prod.isUnit_iff (x := (x : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))) (and_congr_left fun _ => ?_)
  exact (Pi.isUnit_iff (M := fun w : InfinitePlace F => w.Completion)).trans (forall_congr' fun _ => isUnit_iff_ne_zero)

theorem eventually_intAt (g : G1 F) : ∀ᶠ v in cofinite, IntAt v g :=
  eventually_all.2 fun i => eventually_all.2 fun j => (g i j).2.2


variable (F) in
def eInf : A F := (1, 0)
theorem one_sub_eInf_mul (b : A F) : (1 - eInf F) * b = (0, b.2) :=
  Prod.ext (by change (1 - 1) * b.1 = 0; simp) (by change (1 - 0) * b.2 = b.2; simp)

def Lev (r : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)) : AddSubgroup (A F) where
  carrier := {x | x.1 = 0 ∧ ∀ v, Valued.v (x.2 v) ≤ r v}
  zero_mem' := ⟨rfl, fun v => by change Valued.v (pv v 0) ≤ _; simp⟩
  add_mem' {x y} hx hy := ⟨by change p1 F (x + y) = 0; rw [map_add (f := _), adeleInfiniteComponent_apply, adeleInfiniteComponent_apply, hx.1, hy.1, add_zero],
    fun v => by change Valued.v (pv v (x + y)) ≤ _; rw [map_add (f := _)]; exact Valuation.map_add_le _ (hx.2 v) (hy.2 v)⟩
  neg_mem' {x} hx := ⟨by change p1 F (-x) = 0; rw [map_neg, adeleInfiniteComponent_apply, hx.1, neg_zero],
    fun v => by change Valued.v (pv v (-x)) ≤ _; rw [map_neg, Valuation.map_neg]; exact hx.2 v⟩

end UpperTheory.ConvolutionTheory.R2

end
