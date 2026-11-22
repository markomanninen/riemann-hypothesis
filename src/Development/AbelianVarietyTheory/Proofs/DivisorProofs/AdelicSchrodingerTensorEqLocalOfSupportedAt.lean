module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SchrLoc

open GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {z : AF F}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z) :
    z = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v z) := by
  have h1 := hz (1 - GlobalTheory.EmbChart.atPlace v 1)
    (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem schr_tens_of_at : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  intro F _ _ ψ v κ _ w h1 h2 φ r hr
  have at_pi {z : κ → AF F} (h : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (z i)) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z :=
    fun u hu => funext fun i => h i u hu
  have at_mul_left (a : AF F) {b : AF F} (hb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) b) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (a * b) := fun u hu => by
    rw [smul_eq_mul, mul_left_comm, show u * b = 0 from hb u hu, mul_zero]
  have at_add {a b : AF F} (ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a) (hb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) b) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (a + b) := fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  have at_sum {ι : Type} (s : Finset ι) {f : ι → AF F} (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact at_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have evFin_invOf_two : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  funext x
  have hr' : r (x + w.1) = r x := hr x w.1 (at_pi h1)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    at_add (at_sum _ fun i _ => at_mul_left _ (h2 i))
      (at_mul_left _ (at_sum _ fun i _ => at_mul_left _ (h2 i)))
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  rw [hr', eq_atPlace_of_at hz, ← psiV_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_add (f := _), map_mul, map_sum, evFin_invOf_two, Pi.add_apply]
  rw [show (fun i => GlobalTheory.AdelicU.evFin F v (x i) + GlobalTheory.AdelicU.evFin F v (w.1 i)) =
    (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i)) from rfl]
  ring

end GlobalTheory.SchrLoc
