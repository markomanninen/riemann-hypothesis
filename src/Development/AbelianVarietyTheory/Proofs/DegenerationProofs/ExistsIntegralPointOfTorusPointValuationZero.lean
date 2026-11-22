module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAdicCompleteOfNe
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.GtDescent

variable {p : ℕ} [Fact p.Prime]

theorem existsUnique_ext {X S : Scheme.{0}} (q : X ⟶ S) [hp : IsProper q] (c : Sp (OO p) ⟶ S)
    (x : Sp (PadicAlgCl p) ⟶ X) (hx : x ≫ q = gPt p ≫ c) : ∃! y : Sp (OO p) ⟶ X, y ≫ q = c ∧ gPt p ≫ y = x := by
  have hv : ValuativeCriterion q := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let Q : ValuativeCommSq q := { R := OO p, K := PadicAlgCl p, i₁ := x, i₂ := c, commSq := ⟨hx⟩ }
  obtain ⟨U⟩ := hv Q
  refine ⟨U.default.l, ⟨U.default.fac_right, U.default.fac_left⟩, fun ψ hψ => ?_⟩
  exact congrArg CommSq.LiftStruct.l (U.uniq ⟨ψ, hψ.2, hψ.1⟩)

theorem exists_ring {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (j : V →+* OO p) [IsLocalHom j]
    (hj : Function.Injective j) (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (hK : ∀ x, (j x : PadicAlgCl p) ∈ K) (s : Finset (OO p)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (f : V →+* W) (κ : W →+* OO p), Function.Injective κ ∧
      IsLocalHom κ ∧ κ.comp f = j ∧ (∀ x ∈ s, x ∈ κ.range) ∧
      IsAdicComplete ((IsLocalRing.maximalIdeal V).map f) W := by
  let K₁ := IntermediateField.adjoin ℚ_[p] ((s.image (OO p).subtype : Finset _) : Set (PadicAlgCl p))
  have : FiniteDimensional ℚ_[p] K₁ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ K₁
  have : FiniteDimensional ℚ_[p] E := IntermediateField.finiteDimensional_sup K K₁
  have hd : IsDiscreteValuationRing (integralClosure ℤ_[p] E) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] E
  have hf : Module.Finite ℤ_[p] (integralClosure ℤ_[p] E) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] E _
  have := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] (integralClosure ℤ_[p] E)
  let κ : integralClosure ℤ_[p] E →+* OO p :=
    (E.val.toRingHom.comp (integralClosure ℤ_[p] E).val.toRingHom).codRestrict (OO p) fun x =>
      (mem_OO_iff _).2 ((mem_integralClosure_padicInt_iff E _).1 x.2)
  have hl : IsLocalHom κ := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have hy' : ((x : E) : PadicAlgCl p) * (y : PadicAlgCl p) = 1 :=
      congrArg (fun z : OO p => (z : PadicAlgCl p)) hy
    have h0 : (x : E) ≠ 0 := by
      intro h0
      rw [h0] at hy'
      simp at hy'
    have hinv : (x : E)⁻¹ ∈ integralClosure ℤ_[p] E := by
      rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv,
        ← eq_inv_of_mul_eq_one_right hy']
      exact (mem_OO_iff _).1 y.2
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  have hκ : Function.Injective κ := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : OO p => (z : PadicAlgCl p)) h))
  let f₁ : V →+* E := ((OO p).subtype.comp j).codRestrict E fun x => (le_sup_left : K ≤ E) (hK x)
  let f : V →+* integralClosure ℤ_[p] E := f₁.codRestrict (integralClosure ℤ_[p] E) fun x =>
    (mem_integralClosure_padicInt_iff E _).2 ((mem_OO_iff _).1 (j x).2)
  have hc : κ.comp f = j := RingHom.ext fun x => rfl
  refine ⟨integralClosure ℤ_[p] E, inferInstance, inferInstance, f, κ, hκ, hl, hc, fun x hx => ?_,
    isAdicComplete_of_ne (fun h => ?_) (fun h => ?_)⟩
  · exact ⟨⟨⟨x, (le_sup_right : K₁ ≤ E) (IntermediateField.subset_adjoin _ _ (by simpa using hx))⟩,
      (mem_integralClosure_padicInt_iff E _).2 ((mem_OO_iff _).1 x.2)⟩, rfl⟩
  · have hi : Function.Injective f := fun a b h => hj (by rw [← hc]; exact congrArg κ h)
    exact IsDiscreteValuationRing.not_a_field V ((Ideal.map_eq_bot_iff_of_injective hi).1 h)
  · have : (IsLocalRing.maximalIdeal V).map f ≤ IsLocalRing.maximalIdeal _ :=
      Ideal.map_le_iff_le_comap.2 fun x hx hu => hx (IsLocalHom.map_nonunit (f := j) x (hu.map κ))
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ this))

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem gPt_j : gPt p ≫ spMap u.j = (TF (R := u.V) (PadicAlgCl p)).hom := by
  change _ = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem exists_intGood : ∃ J, u.IntGood J := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have hL := u.D.toPre.P.isLB
  have H : ∀ x : Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left, ∃ i, ∀ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left,
      ψ ≫ u.D.toPre.P.A.hom = spMap u.j → gPt p ≫ ψ = x → ⊤ ≤ ψ ⁻¹ᵁ u.D.toPre.P.L.U i := fun x => by
    by_cases h : ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧ gPt p ≫ ψ = x
    · obtain ⟨ψ, h₁, h₂⟩ := h
      obtain ⟨i, hi⟩ := exists_chart hL (ψ (cpt (OO p)))
      refine ⟨i, fun ψ' h₁' h₂' => ?_⟩
      obtain rfl : ψ' = ψ := (existsUnique_ext u.D.toPre.P.A.hom (spMap u.j) x
        (by rw [← h₂, Category.assoc, h₁])).unique ⟨h₁', h₂'⟩ ⟨h₁, h₂⟩
      exact (top_le_iff_cpt _ _).2 hi
    · obtain ⟨i, -⟩ := exists_chart hL (x (cpt (PadicAlgCl p)))
      exact ⟨i, fun ψ h₁ h₂ => (h ⟨ψ, h₁, h₂⟩).elim⟩
  choose J hJ using H
  exact ⟨J, fun ψ h => hJ _ ψ h rfl⟩

theorem spMap_cpt {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    spMap f (cpt B) = cpt A := IsLocalRing.comap_closedPoint f

theorem gtφT_over {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (b : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) : DegPre.gtφT D T b χ k ≫ D.P.A.hom = T.hom := by
  fin_cases k <;> exact Over.w _

theorem exists_model (hl : IsLocalHom u.j) (hj : Function.Injective u.j) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (hK : ∀ x, (u.j x : PadicAlgCl p) ∈ K) (g : GtPtF u.D.toPre (PadicAlgCl p))
    (hg : u.GtN g 0) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (f : u.V →+* W) (κ : W →+* OO p),
      IsLocalHom κ ∧ κ.comp f = u.j ∧ IsAdicComplete ((IsLocalRing.maximalIdeal u.V).map f) W ∧
      ∃ ξ : GtPt u.D.toPre (Over.mk (spMap f)), spMap ((OO p).subtype.comp κ) ≫ ξ.b.left = g.b.left ∧
        ∀ χ z J, Good u.D.toPre.P.L z J →
          val (ξ.s χ) (spMap ((OO p).subtype.comp κ)) z J = val (g.s χ) (𝟙 _) z J := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have hL := u.D.toPre.P.isLB
  obtain ⟨J, hJ⟩ := exists_intGood u
  obtain ⟨b₀, ⟨hb₁, hb₂⟩, -⟩ := existsUnique_ext u.D.toPre.P.A.hom (spMap u.j) g.b.left
    ((Over.w g.b).trans (gPt_j u).symm)
  obtain ⟨s₀, hs₀⟩ := exists_factor u.D.toPre.P.A.hom u.j b₀ hb₁
  have : AddGroup.FG u.D.toPre.X := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨X₀, hX₀⟩ := (AddGroup.fg_iff_addMonoid_fg.1 this).fg_top
  have hv : ∀ χ, ‖valF (𝟙 (Sp (PadicAlgCl p))) _
      ((g.s χ).s (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖ = 1 := fun χ => by
    rw [hg J hJ χ]; simp
  let v : u.D.toPre.X → OO p := fun χ => ⟨_, (mem_OO_iff _).2 (hv χ).le⟩
  have hu : ∀ χ, IsUnit (v χ) := fun χ => by
    by_contra h
    exact ((not_isUnit_OO_iff _).1 h).ne (hv χ)
  obtain ⟨W, _, _, f, κ, hκ, hκl, hc, hs, hW⟩ := exists_ring u.j hj K hK (s₀ ∪ X₀.image v)
  obtain ⟨b', hb₃, hb₄⟩ := hs₀ W f κ hκ hc fun x hx => hs x (Finset.mem_union_left _ hx)
  have eκ : spMap ((OO p).subtype.comp κ) = gPt p ≫ spMap κ := by
    rw [← Spec.map_comp]; rfl
  have ef : spMap κ ≫ spMap f = spMap u.j := by
    rw [← Spec.map_comp, ← hc]; rfl
  let π : TF (R := u.V) (PadicAlgCl p) ⟶ Over.mk (spMap f) := Over.homMk (spMap ((OO p).subtype.comp κ)) (by
    rw [← gPt_j, ← ef, eκ]; exact Category.assoc _ _ _)
  let b : Over.mk (spMap f) ⟶ u.D.toPre.P.A := Over.homMk b' hb₃
  have hb : spMap ((OO p).subtype.comp κ) ≫ b' = g.b.left := by rw [eκ, Category.assoc, hb₄, hb₂]
  let ξ' : GtPt u.D.toPre (TF (R := u.V) (PadicAlgCl p)) := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  have hX : AddSubmonoid.closure ((Subtype.val : (⊤ : AddSubmonoid u.D.toPre.X) → u.D.toPre.X) '' (X₀ : Set _)) = ⊤ := by
    apply top_unique
    intro χ _
    have hh : ∀ x : (⊤ : AddSubmonoid u.D.toPre.X), x ∈ AddSubsemigroup.closure (X₀ : Set _) →
        (x : u.D.toPre.X) ∈ AddSubmonoid.closure ((Subtype.val : (⊤ : AddSubmonoid u.D.toPre.X) → u.D.toPre.X) '' (X₀ : Set _)) := by
      intro x hx
      induction hx using AddSubsemigroup.closure_induction with
      | mem x hx => exact AddSubmonoid.subset_closure ⟨x, hx, rfl⟩
      | add x y hx hy ihx ihy => exact AddSubmonoid.add_mem _ ihx ihy
    apply hh ⟨χ, trivial⟩
    rw [hX₀]
    trivial
  obtain ⟨ξ, h₁, h₂⟩ := exists_descend π (appTop_injective _ (Subtype.val_injective.comp hκ)) ξ' b
    (Over.OverMorphism.ext hb) _ hX fun χ hχ => by
      obtain ⟨χ₀, hχ₀, hχeq⟩ := hχ
      subst χ
      obtain ⟨a, ha⟩ := hs (v χ₀) (Finset.mem_union_right _ (Finset.mem_image_of_mem v (by simpa [Finset.bind_def, Finset.pure_def] using hχ₀)))
      have hau : IsUnit a := IsLocalHom.map_nonunit (f := κ) a (ha ▸ hu χ₀)
      have hφ : ∀ k, spMap ((OO p).subtype.comp κ) ≫ DegPre.gtφT u.D.toPre _ b χ₀ k =
          DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ₀ k := fun k => by
        have := (TorusCoord.comp_eq_of_left b g.b (spMap ((OO p).subtype.comp κ)) (𝟙 _)
          (hb.trans (Category.id_comp _).symm)).1 χ₀ k
        rw [Category.id_comp, ← TorusCoord.gtφT_eq] at this
        exact this
      refine exists_gen_extend hL ((OO p).subtype.comp κ) hφ (g.s χ₀) (g.isGen χ₀)
        (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ₀ k)) ?_ hau.unit (congrArg Subtype.val ha)
      refine (top_le_iff_cpt (𝟙 (Sp W)) (LB.wchart u.D.toPre.P.L (DegPre.gtφT u.D.toPre _ b χ₀)
        (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ₀ k)))).2 ?_
      refine Set.mem_iInter.2 fun k => ?_
      have h3 := (top_le_iff_cpt _ _).1 (hJ (spMap κ ≫ DegPre.gtφT u.D.toPre _ b χ₀ k)
        ((Category.assoc _ _ _).trans ((congrArg _ (gtφT_over b χ₀ k)).trans ef)))
      rw [← Category.assoc, ← eκ, hφ k, Scheme.Hom.comp_apply, spMap_cpt] at h3
      exact h3
  exact ⟨W, inferInstance, inferInstance, f, κ, hκl, hc, hW, ξ, by rw [h₁]; exact hb, h₂⟩

theorem exists_integral_point : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)), u.GtN g 0 → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ u.Lev c g := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u g hg
  obtain ⟨-, hl, hj, K, hK, hK'⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  obtain ⟨W, _, _, f, κ, hκ, hc, hW, ξ, h₁, h₂⟩ := exists_model u hl hj K (fun x => by
    rw [← SetLike.mem_coe, hK']; exact ⟨_, rfl⟩) g hg
  have hL := u.D.toPre.P.isLB
  obtain ⟨x, hx, -⟩ := FormalPoint.existsUnique_isPointOf u.U.toUnifPre ξ
  have eκ : spMap ((OO p).subtype.comp κ) = gPt p ≫ spMap κ := by
    rw [← Spec.map_comp]; rfl
  have ef : spMap κ ≫ spMap f = spMap u.j := by
    rw [← Spec.map_comp, ← hc]; rfl
  refine ⟨spMap κ ≫ x.left, (Category.assoc _ _ _).trans ((congrArg _ (Over.w x)).trans ef),
    spMap κ ≫ ξ.b.left, by rw [← Category.assoc, ← eκ, h₁], fun e ce hce => ?_⟩
  obtain ⟨a₁, a₂⟩ := (FormalPoint.hasCoords_iff _ _ _ _ _).1
    (hx e _ (spMap (Ideal.Quotient.mk (u.lev e)) ≫ spMap κ) ce (hce.trans (Category.assoc _ _ _).symm))
  refine ⟨a₁.trans (Category.assoc _ _ _), fun χ jj hjj => ?_⟩
  have hne : u.lev e ≠ ⊤ := fun h => by
    have : u.lev e ≤ IsLocalRing.maximalIdeal _ := Ideal.map_le_iff_le_comap.2 fun x hx hu =>
      Ideal.pow_le_self e.succ_ne_zero hx (IsLocalHom.map_nonunit (f := u.j) x hu)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ this))
  have : Nontrivial (OO p ⧸ u.lev e) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (OO p ⧸ u.lev e) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (u.lev e)) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hφ := (TorusCoord.comp_eq_of_left ξ.b (u.U.gt e).pG _ ce a₁.symm).1 χ
  have hφ' : ∀ k, spMap ((OO p).subtype.comp κ) ≫ DegPre.gtφT u.D.toPre _ ξ.b χ k =
      𝟙 _ ≫ DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k := fun k => by
    have := (TorusCoord.comp_eq_of_left ξ.b g.b (spMap ((OO p).subtype.comp κ)) (𝟙 _)
      (h₁.trans (Category.id_comp _).symm)).1 χ k
    rw [← TorusCoord.gtφT_eq] at this
    exact this
  have hm := mem_wchart_of_eq _ _ (fun k => (hφ k).symm) _ ((top_le_iff_cpt _ _).1 hjj)
  rw [Scheme.Hom.comp_apply, spMap_cpt] at hm
  have ht := (top_le_iff_cpt (spMap κ) _).2 hm
  obtain ⟨t₁, v₁⟩ := CrdCalc.valR_spMap (OO p).subtype (spMap κ) _ ht
  obtain ⟨t₂, v₂⟩ := CrdCalc.valR_spMap (Ideal.Quotient.mk (u.lev e)) (spMap κ) _ ht
  refine ⟨valR (spMap κ) _ ((ξ.s χ).s jj).val, (v₁ _).symm.trans ?_, (v₂ _).symm.trans ?_⟩
  · rw [← eκ] at t₁ ⊢
    exact valR_transfer hL (ξ.isGen χ) (g.isGen χ) _ (𝟙 _) hφ' (h₂ χ) t₁
  · exact valR_transfer hL (ξ.isGen χ) ((u.U.gt e).t_gen χ) _ ce hφ (fun z J hJ => (a₂ χ z J hJ).symm) t₂

end GlobalTheory.GtDescent
end
