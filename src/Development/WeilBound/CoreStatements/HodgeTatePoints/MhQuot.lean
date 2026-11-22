module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MhBase
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorBtOrderStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

theorem quot : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (H : Type) [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] (α : H →* T), (∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) → IsFinite Γ₁.G.hom → IsFinite Γ.G.hom → Flat a.left → Surjective a.left → quotOrder α (Γ₁.btOrder ⊤) = Γ.btOrder ⊤ := by
  intro R _ _ _ T _ _ Γ H _ _ Γ₁ a _ α hpt hfin₁ hfin hfl hsurj
  haveI : IsAffine Γ.G.left := isAffine_of_isAffineHom Γ.G.hom
  haveI : IsAffine Γ₁.G.left := isAffine_of_isAffineHom Γ₁.G.hom
  have hα : Function.Surjective α := by
    intro t
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    obtain ⟨y, hy⟩ := a.left.surjective ((Γ.pt t).left z)
    have hgen : (Γ₁.G.hom y).asIdeal = ⊥ := by
      have e1 : Γ₁.G.hom y = Γ.G.hom ((Γ.pt t).left z) := by
        rw [← hy, ← Scheme.Hom.comp_apply, Over.w a]
      rw [e1, ← Scheme.Hom.comp_apply, Over.w (Γ.pt t)]
      show (PrimeSpectrum.comap (algebraMap R (FractionRing R)) z).asIdeal = ⊥
      rw [PrimeSpectrum.comap_asIdeal]
      have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.isPrime.ne_top
      rw [hz]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    obtain ⟨h, x, hx⟩ := Γ₁.pt_onto y hgen
    refine ⟨h, Γ.pt_inj (α h) t x z ?_⟩
    have e2 : a.left ((Γ₁.pt h).left x) = (Γ.pt (α h)).left x := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hpt h]
    rw [← e2, hx, hy]
  have valAt_top : ∀ {B : Type} [CommRing B] {X : Scheme.{0}}
      (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)),
      valAt x ⊤ h s = val x s := by
    intro B _ X x h s
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have sec_ext : ∀ {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)}, (∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') → s = s' := by
    intro T _ _ Γ s s' h
    rw [← sub_eq_zero]
    refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
    rw [valAt_top, map_sub, h, sub_self]
  have mem_top_iff : ∀ {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → R), f ∈ Γ.btOrder ⊤ ↔
      ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
    intro T _ _ Γ f
    have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
        (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
      intro B _ X x U hx a b
      simp only [valAt, map_sub]
    constructor
    · intro hf t
      rw [Twhopf.mem_order] at hf
      have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
          ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
            valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
        fun g => hf t g (by simp)
      choose U hgU s hs using hreg
      obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
        (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
          intro g g'
          rw [← sub_eq_zero]
          apply Twhopf.sec_inj R T Γ _ _
          intro h hh
          have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
            (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
          have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
            (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
          refine (hsub _ _ hh _ _).trans ?_
          erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
          rw [hs, hs, sub_self])
      refine ⟨g0, fun h => ?_⟩
      have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
      let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
      have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
        Twhopf.top_le_of_mem _ z (hgU _)
      refine (valAt_top _ htop g0).symm.trans ?_
      refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
      erw [hglue ((Γ.pt h).left z)]
      exact hs _ h hh
    · intro hf
      rw [Twhopf.mem_order]
      intro t g _
      obtain ⟨s, hs⟩ := hf t
      unfold QFGroup.RegularAt
      exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩
  ext f
  rw [quotOrder, Subalgebra.mem_comap, mem_top_iff, mem_top_iff]
  constructor
  · intro hf t
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank R T Γ
    obtain ⟨s0, hs0⟩ := (mem_top_iff Γ _).1 (hd (fun x => f (t * x))) 1
    obtain ⟨h0, rfl⟩ := hα t
    obtain ⟨s₁, hs₁⟩ := hf h0
    have key : a.left.appTop s0 = a.left.appTop (pb Γ.G.hom d) * s₁ := by
      apply sec_ext Γ₁
      intro h
      rw [map_mul, ← val_comp, ← val_comp, ← Over.comp_left, hpt h, hs0, val_pb (Over.w (Γ.pt (α h))), hs₁, ← map_mul]
      congr 1
      show d * f (α h0 * (1 * α h)) = d * f (α (h0 * h))
      rw [_root_.one_mul, MonoidHom.map_mul]
    have e : Spec.map a.left.appTop = Γ₁.G.left.isoSpec.inv ≫ a.left ≫ Γ.G.left.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    have hff : a.left.appTop.hom.FaithfullyFlat :=
      (flat_and_surjective_SpecMap_iff _).1 ⟨by rw [e]; infer_instance, by rw [e]; infer_instance⟩
    letI : Algebra Γ(Γ.G.left, ⊤) Γ(Γ₁.G.left, ⊤) := a.left.appTop.hom.toAlgebra
    have hmem : s0 ∈ Ideal.span {pb Γ.G.hom d} := by
      rw [← @Ideal.comap_map_eq_self_of_faithfullyFlat _ _ _ _ _ hff (Ideal.span {pb Γ.G.hom d}),
        Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact ⟨s₁, key⟩
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨s, fun h => ?_⟩
    have e3 := hs0 h
    rw [← hs, map_mul, val_pb (Over.w (Γ.pt h))] at e3
    have hd' : algebraMap R (FractionRing R) d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hd0
    apply mul_right_cancel₀ hd'
    rw [e3, ← map_mul]
    congr 1
    show d * f (α h0 * (1 * h)) = f (α h0 * h) * d
    rw [_root_.one_mul, mul_comm]
  · intro hf h0
    obtain ⟨s, hs⟩ := hf (α h0)
    refine ⟨a.left.appTop s, fun h => ?_⟩
    rw [← val_comp, ← Over.comp_left, hpt h, hs]
    exact congrArg _ (congrArg f (map_mul α h0 h).symm)

end PositivityTheory.HtPt.Mh
