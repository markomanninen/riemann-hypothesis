module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open GlobalTheory.EtC.KumCoker in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cokernel_to_multiplicativeGroup_bijective : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0),
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U)) := by
  intro q _ κ h0 H1 H2
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have key : ∀ {V : Scheme.{0}} (b : Sec Gm V), Sec.map qb (Sec.map (cokernel.π κ) b) = Sec.map ((q : ℤ) • 𝟙 Gm) b := by
    intro V b
    rw [← sec_map_comp, hqb, cokernel.π_desc]
  have hls : Sheaf.IsLocallySurjective (cokernel.π κ) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  have inj : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Injective (Sec.map qb (U := U)) := by
    intro U hU
    refine (injective_iff_map_eq_zero ((qb.hom.app (op U)).hom)).2 (fun c hc => ?_)
    have hc' : Sec.map qb c = 0 := hc
    apply sec_eq_zero
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (cokernel.π κ).hom c, fun V g hg => ?_⟩
    obtain ⟨b, hb⟩ := hg
    have hb' : Sec.map (cokernel.π κ) b = Sec.res g c := hb
    have hz : Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 := by
      rw [← key, hb', ← sec_nat, hc', sec_res_zero]
    obtain ⟨a, rfl⟩ := H1 V (unit_res hU g) b hz
    rw [← hb', ← sec_map_comp, cokernel.condition, sec_map_zero]
  intro U hU
  refine ⟨inj U hU, fun b => ?_⟩
  obtain ⟨S, hS, hP⟩ := H2 U hU b
  choose c hc using hP
  let x : Presieve.FamilyOfElements ((cokernel κ).obj ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) S.arrows :=
    fun V g hg => Sec.map (cokernel.π κ) (c V g hg)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ w
    apply inj Z (unit_res hU (f₁ ≫ g₁))
    change Sec.map qb (Sec.res f₁ (Sec.map (cokernel.π κ) (c _ g₁ hg₁))) =
      Sec.map qb (Sec.res f₂ (Sec.map (cokernel.π κ) (c _ g₂ hg₂)))
    rw [← sec_nat, ← sec_nat, key, key, hc, hc, sec_res_comp, sec_res_comp, w]
  obtain ⟨t, ht, -⟩ := isSheaf_forget (cokernel κ) S hS x hx
  refine ⟨t, sub_eq_zero.1 (sec_eq_zero Gm _ ⟨S, hS, fun V g hg => ?_⟩)⟩
  have ht' : Sec.res g t = Sec.map (cokernel.π κ) (c V g hg) := ht g hg
  change (Gm.obj.map g.op).hom (Sec.map qb t - b) = 0
  rw [map_sub]
  change Sec.res g (Sec.map qb t) - Sec.res g b = 0
  rw [sec_nat, ht', key, hc, sub_self]
