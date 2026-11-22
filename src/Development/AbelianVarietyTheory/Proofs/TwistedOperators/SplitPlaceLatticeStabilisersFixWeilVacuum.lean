module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

private theorem selfDual_full {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
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

private theorem det_int {D : D7} {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsFullLattice D.host.E L) (g : GA D V)
    (h : ∀ y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)),
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E))) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hL.toIsLattice.fg hL.span_eq_top h

private theorem unram_detAt {D : D7} {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsFullLattice D.host.E L) {g : GA D V}
    (h : ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)))
    {e : AE D} (he : e * e = e) {ε : AF D.host.F} (hs : algebraMap (AF D.host.F) (AE D) ε * e = e)
    {χ : (AE D)ˣ →* Circle} (hχ : GlobalTheory.WeilParts.UnramAt ε χ) : χ (GlobalTheory.VecInv.detAt e he V g) = 1 := by
  refine hχ _ ?_ (GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g fun y hy => (h y).1 hy)) ?_
  · change _ * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
    linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hs
  · rw [← MonoidHom.map_inv]
    exact GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g⁻¹ (GlobalTheory.LocalLatStab.inv_keeps V _ g h))


theorem splitVacuumFixed : ∀ D : D7, SplitVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  obtain ⟨e, he, hb⟩ := hv
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hb' : e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := hb
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have s1 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * e = e := by
    rw [← hb']; linear_combination he.1 + he.2.1
  have s2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * cA D e = cA D e := by
    rw [← hb']; linear_combination he'.1 + he.2.1
  have sk := suppPl_emb S v k
  have sk' := suppPl_emb T v k'
  have kS := emb_keeps_latHat S hS.1.fg v hk
  have kT := emb_keeps_latHat T hT.1.fg v hk'
  have key := GlobalTheory.VacStabFixed.om_split_halves hW hS hT he (fun i j => by rw [hb']; exact sk i j)
    (fun i j => by rw [hb']; exact sk' i j)
    (fun u hu => ⟨GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (fun y hy => (kS y).1 hy) (fun y hy => (kT y).1 hy) u hu,
      GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (GlobalTheory.LocalLatStab.inv_keeps S _ _ kS)
        (GlobalTheory.LocalLatStab.inv_keeps T _ _ kT) u hu⟩)
    (GlobalTheory.VecInv.isDetAt_detAt e he.1 S _) (GlobalTheory.VecInv.isDetAt_detAt e he.1 T _) hf
    (fun u hu hh => hvac.2 e he u (GlobalTheory.VacStabFixed.half_mem_place hε s1 hu hh) hh)
    (fun u hu hh => hvac.2 _ he' u (GlobalTheory.VacStabFixed.half_mem_place hε s2 hu hh) hh)
  rwa [splitFacO, unram_detAt (selfDual_full S ΛS hS) kS he.1 s1 uT, unram_detAt (selfDual_full T ΛT hT) kT he.1 s1 uS,
    inv_one, mul_one, Circle.coe_one, one_smul] at key

end GlobalTheory.PlaceTensor

end
