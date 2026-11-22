module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionEqOfLocalAgreement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FinPl.LocGlob

variable {D : D7}

theorem swap_finPart_pure (α : Af D.host.F) (e : D.host.E) :
    Formalism.IndefR.Lev.swapAE D (finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e)) = e ⊗ₜ[D.host.F] α := by
  have h1 : finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
    unfold finPart
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    rfl
  rw [h1]
  rfl

theorem mem_of_local {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (z : Fin S.rank → D.host.E)
    (hz : ∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈
      GlobalTheory.FinPl.latV S L (· = v)) : z ∈ L := by
  classical
  have hlat := hL.1
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have hspan := Submodule.IsFullLattice.span_eq_top (self := hfull S L hL)
  obtain ⟨d, hd, hdz⟩ := GlobalTheory.FinPl.exists_int_smul_le (Submodule.span (𝓞 D.host.E) {z}) L
    (Submodule.fg_span_singleton z) hspan
  set T := (GlobalTheory.FinPl.finite_places_int (D := D) d hd).toFinset with hT
  set β : Af D.host.F := 1 - ∑ v ∈ T, GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) with hβ
  have hβv : ∀ w, evalV D.host.F w β = if w ∈ T then 0 else 1 := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hβ, map_sub, map_one, map_sum]
    simp only [GlobalTheory.FinPl.LatMem.evalV_indP]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  have hoff : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) ∈
      GlobalTheory.FinPl.latV S L (fun w => w ∉ T) := by
    apply GlobalTheory.FinPl.LocAgree.latV_le_of_int_smul_on S (Submodule.span (𝓞 D.host.E) {z}) L d hd hdz
    · intro v hv hmem
      exact hv ((Set.Finite.mem_toFinset _).2 hmem)
    · apply AddSubgroup.subset_closure
      refine ⟨β, fun w => ?_, fun w hw => ?_, 1, rfl, z, Submodule.mem_span_singleton_self z, rfl⟩
      · rw [hβv]
        split_ifs
        · exact zero_mem _
        · exact one_mem _
      · rw [hβv, if_pos (not_not.1 hw)]
  have hall : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    have e : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) =
        ∑ v ∈ T, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) +
          (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) := by
      funext i
      rw [Pi.add_apply, Finset.sum_apply, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.add_tmul]
      congr 1
      have hpa : ∀ a b : Af D.host.F, pairA D.host.F 0 a + pairA D.host.F 0 b = pairA D.host.F 0 (a + b) :=
        fun a b => Prod.ext (add_zero 0) rfl
      have hsum : ∀ (s : Finset (Pl D)) (f : Pl D → Af D.host.F),
          ∑ v ∈ s, pairA D.host.F 0 (f v) = pairA D.host.F 0 (∑ v ∈ s, f v) := by
        intro s f
        induction s using Finset.induction_on with
        | empty => exact Prod.ext rfl rfl
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, hpa]
      rw [hsum, hpa, hβ, add_sub_cancel]
    rw [e]
    exact add_mem (sum_mem fun v _ => GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) (hz v))
      (GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) hoff)
  have hhat := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ hall
  have e2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (z i) := by
    funext i
    rw [swap_finPart_pure]
    rfl
  rw [e2] at hhat
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff hlat.fg hspan z).1 hhat

theorem mem_of_mem_latV_all : ∀ {D : D7} {S : HSp D} {L : Lat S}, IsSelfDualC S L → (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) :=
  fun hL z hz => mem_of_local hL z hz

end GlobalTheory.FinPl.LocGlob
