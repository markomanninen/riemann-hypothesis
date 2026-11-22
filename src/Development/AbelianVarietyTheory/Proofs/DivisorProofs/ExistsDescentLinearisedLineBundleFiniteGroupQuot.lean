module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecResidueFieldCompAutEqOfFixesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantLocalEquationCartierFiniteQuotienStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorGroupQuotientDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEqStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.QuotDescent

private theorem descent_algebraMap_stalkCongr_of_eq {X : Scheme.{0}} [IsIntegral X] {x y : X} (h : x = y)
    (a : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk y) X.functionField ((X.presheaf.stalkCongr (.of_eq h)).hom a) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
  subst h
  simp

private theorem descent_fromSpecResidueField_comp_eq_of_fixes (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ]
    (ρ : Γ →* Aut X) (γ : Γ) (x : X) (hx : (ρ γ).asIso.hom x = x)
    (h : ∀ u : X.functionFieldˣ, RegAt x u → ZeroAt x ((fnAct ρ γ u : X.functionField) - u)) :
    X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x := by
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  set φ := (ρ γ).asIso.hom with hφ
  have key : (X.residueFieldCongr hx.symm).hom ≫ φ.residueFieldMap x = 𝟙 _ := by
    rw [← cancel_epi (X.residue x), Category.comp_id, X.residue_residueFieldCongr_assoc,
      Scheme.residue_residueFieldMap]
    ext a
    change IsLocalRing.residue _ (φ.stalkMap x ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom a)) =
      IsLocalRing.residue _ a
    set b := (X.presheaf.stalkCongr (.of_eq hx.symm)).hom a with hb
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    by_cases ha : a = 0
    · rw [hb, ha, map_zero, map_zero, sub_zero]
      exact zero_mem _
    · have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
      obtain ⟨c, hc, e⟩ := h (Units.mk0 _ hne) ⟨a, rfl⟩
      have e2 : ((fnAct ρ γ (Units.mk0 _ hne) : X.functionFieldˣ) : X.functionField) =
          GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) := rfl
      have e4 : GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) =
          algebraMap (X.presheaf.stalk x) X.functionField (φ.stalkMap x b) := by
        rw [← descent_algebraMap_stalkCongr_of_eq hx.symm a, ← hb]
        exact GlobalTheory.functionFieldMap_algebraMap φ x b
      rw [e2, Units.val_mk0, e4, ← map_sub] at e
      rwa [← IsFractionRing.injective _ _ e]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← X.residueFieldCongr_fromSpecResidueField hx.symm, ← Category.assoc, ← Spec.map_comp, key,
    Spec.map_id, Category.id_comp]


theorem functionFieldMap_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
  have e : Spec.map (CommRingCat.ofHom (functionFieldMap (a ≫ b))) ≫ genericFieldPoint Z =
      Spec.map (CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b))) ≫
        genericFieldPoint Z := by
    rw [specMap_functionFieldMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      specMap_functionFieldMap, ← Category.assoc, ← Category.assoc, specMap_functionFieldMap]
  haveI : Mono (genericFieldPoint Z) := inferInstanceAs (Mono (Z.fromSpecStalk _))
  have := Spec.map_injective ((cancel_mono _).mp e)
  exact congrArg CommRingCat.Hom.hom this

theorem fnAct_mul : ∀ (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ] (ρ : Γ →* Aut X) (γ δ : Γ)
    (u : X.functionFieldˣ), fnAct ρ (γ * δ) u = fnAct ρ δ (fnAct ρ γ u) := by
  intro X _ Γ _ ρ γ δ u
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  haveI : IsIso (ρ δ).asIso.hom := Iso.isIso_hom (ρ δ).asIso
  haveI : IsIso (ρ (γ * δ)).asIso.hom := Iso.isIso_hom (ρ (γ * δ)).asIso
  have hc : (ρ (γ * δ)).asIso.hom = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom := by
    rw [map_mul, Aut.mul_asIso]; rfl
  apply Units.ext
  change functionFieldMap (ρ (γ * δ)).asIso.hom (u : X.functionField) =
    functionFieldMap (ρ δ).asIso.hom (functionFieldMap (ρ γ).asIso.hom (u : X.functionField))
  have key : ∀ (f : X ⟶ X) (_ : IsDominant f), f = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom →
      functionFieldMap f (u : X.functionField) =
        functionFieldMap (ρ δ).asIso.hom (functionFieldMap (ρ γ).asIso.hom (u : X.functionField)) := by
    rintro f _ rfl
    rw [functionFieldMap_comp]
    rfl
  exact key _ inferInstance hc

theorem descent : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ W) (sW : W ⟶ Sp F) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB), IsProjOver (q ≫ sW) → IsAffineQuotient ρ q → RatLin ρ L hL → ∃ (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = cls L hL := by
  intro F _ _ X W _ q sW Γ _ _ ρ L hL _ hq hR
  obtain ⟨D, c, hcls, hcoc, heq, hin⟩ := hR
  haveI : IsIntegral W := hq.isIntegral
  haveI : Surjective q := hq.surjective
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (toFunctionField (q ≫ sW)).injective
  let σ : Γ → X.functionField →+* X.functionField := fun γ =>
    haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso; functionFieldMap (ρ γ).asIso.hom
  have hσu : ∀ γ (u : X.functionFieldˣ), ((fnAct ρ γ u : X.functionFieldˣ) : X.functionField) = σ γ u :=
    fun _ _ => rfl
  have hσ : ∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a) := by
    intro γ δ a
    by_cases ha : a = 0
    · simp [ha]
    · have := congrArg Units.val (fnAct_mul X Γ ρ γ δ (Units.mk0 a ha))
      rwa [hσu, hσu, hσu] at this
  have hcoc' : ∀ γ δ, (c (γ * δ) : X.functionField) = σ δ (c γ) * c δ := fun γ δ => by
    rw [hcoc, Units.val_mul, hσu]
  have htriv : ∀ γ, (∀ a, σ γ a = a) → c γ = 1 := by
    intro γ hγ
    have hη : (ρ γ).asIso.hom (genericPoint X) = genericPoint X := by
      haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
      have h1 := (genericPoint_spec X).image (ρ γ).asIso.hom.continuous
      have hs : Function.Surjective (ρ γ).asIso.hom.base := (ρ γ).asIso.hom.surjective
      simp only [Set.top_eq_univ, Set.image_univ, hs.range_eq, closure_univ] at h1
      exact h1.eq (genericPoint_spec X)
    have hfix := descent_fromSpecResidueField_comp_eq_of_fixes X Γ ρ γ (genericPoint X) hη (fun u _ => by rw [hσu, hγ, sub_self]; exact zeroAt_zero _)
    have h0 := hin γ _ 1 hfix (D.isEqn_genericPoint 1)
    have h1 : ((fnAct ρ γ 1 * (c γ)⁻¹ * 1⁻¹ : X.functionFieldˣ) : X.functionField) - 1 = 0 := by
      by_contra hne
      exact (zeroAt_iff.1 h0).2 (unitAt_genericPoint hne)
    rw [map_one, one_mul, inv_one, mul_one, sub_eq_zero, ← Units.val_one, Units.val_inj, inv_eq_one] at h1
    exact h1
  obtain ⟨f, hf⟩ := GlobalTheory.T.hilbert90_finite_rightAction_charZero_field _ Γ σ hσ c hcoc' htriv
  have hfu : ∀ γ, fnAct ρ γ f = c γ * f := fun γ => Units.ext (by rw [hσu, Units.val_mul]; exact hf γ)
  set D' := D - CartierDiv.principal f with hD'
  have hD : D' + CartierDiv.principal f = D := sub_add_cancel _ _
  have hinv' : ∀ γ x g, D'.IsEqn ((ρ γ).asIso.hom x) g → D'.IsEqn x (fnAct ρ γ g) := by
    intro γ x g h
    have h1 := heq γ x (g * f) (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f _))
    have h2 := h1.sub (CartierDiv.isEqn_principal f x)
    have e : fnAct ρ γ g = fnAct ρ γ (g * f) * (c γ)⁻¹ / f := by
      rw [map_mul, hfu]; simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h2
  have hin' : ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D'.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1) := by
    intro γ x g hx h
    have h1 := hin γ x (g * f) hx (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f x))
    have e : fnAct ρ γ g * g⁻¹ = fnAct ρ γ (g * f) * (c γ)⁻¹ * (g * f)⁻¹ := by
      rw [map_mul, hfu]; simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h1
  have hloc := GlobalTheory.T.exists_invariant_localEquation_cartier_finiteQuotient F X W (q ≫ sW) Γ ρ q hq D' hinv' hin'
  have key : ∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y →
      D'.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
    intro y
    obtain ⟨x, rfl⟩ := q.surjective y
    obtain ⟨g, hg, hgx⟩ := hloc x
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant X W Γ ρ q hq g hg
    refine ⟨b, fun x' hx' => ?_⟩
    obtain ⟨γ, rfl⟩ := (hq.apply_eq_iff x x').1 hx'.symm
    rw [hb]
    have hp : (ρ γ⁻¹).asIso.hom ((ρ γ).asIso.hom x) = x := by
      rw [map_inv]
      exact Scheme.inv_hom_apply _ _
    have := hinv' γ⁻¹ ((ρ γ).asIso.hom x) g (by rw [hp]; exact hgx)
    rwa [hg] at this
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_cartierDivisor_group_quotient_descent X W Γ ρ q hq D' key
  refine ⟨toLB E, isLB_toLB E, ?_⟩
  rw [GlobalTheory.T.cechPicardPullback_cartierDivisorBundle_eq X W q D' E hE]
  calc cls (toLB D') (isLB_toLB D') = toPic D' := (toPic_apply D').symm
    _ = toPic D := by rw [hD', map_sub, toPic_principal, sub_zero]
    _ = cls L hL := hcls

end GlobalTheory.QuotDescent
