module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigCover

theorem exists_gen_of_chart {Y P : Scheme.{0}} {M : LB P} (hM : M.IsLB) (f : Y ⟶ P) (i : M.ι)
    (hf : ∀ y, f y ∈ M.U i) : ∃ t : LB.Gen (M.pull f), t.IsGen := by
  have le (J : (M.pull f).ι) : (M.pull f).U J ≤ f ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U i) :=
    fun y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => Units.map (f.appLE _ _ (le J)).hom.toMonoidHom (M.g (J PUnit.unit) i)⟩, ?_⟩
  intro J J'
  let j := J PUnit.unit
  let k := J' PUnit.unit
  let U := (M.pull f).U J ⊓ (M.pull f).U J'
  let V := M.U j ⊓ M.U k ⊓ M.U i
  have hUV : U ≤ f ⁻¹ᵁ V := fun y hy => ⟨⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩, hf y⟩
  let pullToU := Units.map (f.appLE V U hUV).hom.toMonoidHom
  have pull_res {A : P.Opens} (h : V ≤ A) (a : Γ(P, A)ˣ) :
      pullToU (res h a) = Units.map (f.appLE A U (hUV.trans (f.preimage_mono h))).hom.toMonoidHom a := by
    apply Units.ext
    exact congrArg (fun q => q.hom a.val) (f.map_appLE hUV (homOfLE h).op)
  have res_pull {A : P.Opens} {B : Y.Opens} (h : B ≤ f ⁻¹ᵁ A) (h' : U ≤ B) (a : Γ(P, A)ˣ) :
      res h' (Units.map (f.appLE A B h).hom.toMonoidHom a) = Units.map (f.appLE A U (h'.trans h)).hom.toMonoidHom a := by
    apply Units.ext
    exact congrArg (fun q => q.hom a.val) (f.appLE_map h (homOfLE h').op)
  have transition : (M.pull f).g J J' = pullToU (res inf_le_left (M.g j k)) := by
    show (∏ _ : PUnit, (res _ (pullU f _ (M.g j k))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one, pull_res]
    rfl
  change res (_ : U ≤ (M.pull f).U J) (Units.map (f.appLE _ _ (le J)).hom.toMonoidHom (M.g j i)) =
    (M.pull f).g J J' * res (_ : U ≤ (M.pull f).U J') (Units.map (f.appLE _ _ (le J')).hom.toMonoidHom (M.g k i))
  calc
    _ = pullToU (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (M.g j i)) :=
      (res_pull (le J) inf_le_left _).trans (pull_res _ _).symm
    _ = pullToU (res inf_le_left (M.g j k)) *
        pullToU (res (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (M.g k i)) := by
      rw [← map_mul]
      exact congrArg pullToU (hM.cocycle j k i).symm
    _ = _ := congrArg₂ (· * ·) transition.symm
      ((pull_res _ _).trans (res_pull (le J') inf_le_right _).symm)

theorem exists_flat_cover_triv : ∀ {P : Scheme.{0}} (M : LB P), M.IsLB → ∃ (Z : Scheme.{0}) (g : Z ⟶ P),
    Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧ Triv (M.pull g) := by
  intro P M hM
  let D : M.ι → Scheme.{0} := fun i => (M.U i).toScheme
  let g : ∐ D ⟶ P := Sigma.desc fun i => (M.U i).ι
  have hι : ∀ i, Sigma.ι D i ≫ g = (M.U i).ι := fun i => Sigma.ι_comp_desc _ i
  refine ⟨∐ D, g, ?_, ?_, ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    have hf : ∀ i : M.ι, Flat (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @Flat) (sigmaOpenCover D) hf
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    have hf : ∀ i : M.ι, LocallyOfFinitePresentation (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) (sigmaOpenCover D) hf
  · refine ⟨fun x => ?_⟩
    obtain ⟨i, hi⟩ := exists_chart hM x
    let x' : D i := ⟨x, hi⟩
    refine ⟨Sigma.ι D i x', ?_⟩
    have e : (Sigma.ι D i ≫ g) x' = x := by rw [hι]; rfl
    exact e
  · let Z := ∐ D
    let σ (s : M.ι) : D s ⟶ Z := Sigma.ι D s
    have cover (y : Z) : ∃ s, y ∈ (σ s).opensRange := by
      obtain ⟨s, x, rfl⟩ := (sigmaOpenCover D).exists_eq y
      exact ⟨s, x, rfl⟩
    have sections (U : Z.Opens) (V : ∀ s, (D s).Opens) (hV : ∀ s, V s = σ s ⁻¹ᵁ U) :
        Function.Bijective (fun a : Γ(Z, U)ˣ => fun s =>
          Units.map ((σ s).appLE U (V s) (hV s).le).hom.toMonoidHom a) := by
      have hv : V = fun s => σ s ⁻¹ᵁ U := funext hV
      subst V
      simp only [Scheme.Hom.appLE_eq_app]
      let E (s : M.ι) := (σ s).opensRange ⊓ U
      let e (s : M.ι) := IsOpenImmersion.ΓIso (σ s) U
      have hc : U ≤ ⨆ s, E s := fun y hy => by
        obtain ⟨s, hs⟩ := cover y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨s, hs, hy⟩
      have restrict (a : Γ(Z, U)) (s : M.ι) :
          (e s).hom.hom (((σ s).app U).hom a) =
            (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom a :=
        congrArg (fun q => q.hom a) (IsOpenImmersion.app_ΓIso_hom (σ s) U)
      have compatible (a : ∀ s, Γ(Z, E s)) : TopCat.Presheaf.IsCompatible Z.sheaf.1 E a := by
        intro s s'
        by_cases he : s = s'
        · subst s'
          rfl
        · apply TopCat.Presheaf.section_ext Z.sheaf (E s ⊓ E s')
          intro y hy
          have hd := disjoint_iff.1 (disjoint_opensRange_sigmaι D s s' he)
          have hm : y ∈ (σ s).opensRange ⊓ (σ s').opensRange := ⟨hy.1.1, hy.2.1⟩
          rw [hd] at hm
          exact hm.elim
      have ext_sections (a b : Γ(Z, U))
          (h : ∀ s, (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom a =
            (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom b) : a = b :=
        Z.sheaf.eq_of_locally_eq' E U (fun _ => homOfLE inf_le_right) hc a b h
      constructor
      · intro a b hab
        apply Units.ext
        apply ext_sections
        intro s
        rw [← restrict, ← restrict]
        exact congrArg (fun u : Γ(D s, σ s ⁻¹ᵁ U)ˣ => (e s).hom.hom u.val)
          (congrFun hab s)
      · intro a
        let b (s : M.ι) : Γ(Z, E s)ˣ := Units.map (e s).hom.hom.toMonoidHom (a s)
        obtain ⟨u, hu, _⟩ := Z.sheaf.existsUnique_gluing' E U (fun _ => homOfLE inf_le_right) hc
          (fun s => (b s).val) (compatible _)
        obtain ⟨v, hv, _⟩ := Z.sheaf.existsUnique_gluing' E U (fun _ => homOfLE inf_le_right) hc
          (fun s => (b s).inv) (compatible _)
        have huv : u * v = 1 := by
          apply ext_sections
          intro s
          simp only [map_mul, map_one]
          exact (congrArg₂ (· * ·) (hu s) (hv s)).trans (b s).val_inv
        refine ⟨⟨u, v, huv, (mul_comm v u).trans huv⟩, funext fun s => ?_⟩
        apply Units.ext
        apply (e s).commRingCatIsoToRingEquiv.injective
        exact (restrict u s).trans (hu s)
    let L := M.pull g
    let Ls (s : M.ι) := M.pull (σ s ≫ g)
    have localGen (s : M.ι) : ∃ t : LB.Gen (Ls s), t.IsGen := by
      refine exists_gen_of_chart hM (σ s ≫ g) s fun y => ?_
      change (Sigma.ι D s ≫ g) y ∈ M.U s
      rw [hι]
      exact y.2
    choose t ht using localGen
    have charts (s : M.ι) (J : L.ι) : (Ls s).U J = σ s ⁻¹ᵁ L.U J := by
      ext y
      exact mem_pull.trans (mem_pull (F := g)).symm
    let pullOn (s : M.ι) (A : Z.Opens) (B : (D s).Opens) (h : B ≤ σ s ⁻¹ᵁ A) :=
      Units.map ((σ s).appLE A B h).hom.toMonoidHom
    have glue (J : L.ι) : ∃ a : Γ(Z, L.U J)ˣ,
        ∀ s, pullOn s _ _ (charts s J).le a = (t s).s J := by
      obtain ⟨a, ha⟩ := (sections (L.U J) (fun s => (Ls s).U J) (fun s => charts s J)).2
        (fun s => (t s).s J)
      exact ⟨a, fun s => congrFun ha s⟩
    choose a ha using glue
    refine ⟨⟨a⟩, ?_⟩
    intro J J'
    let U := L.U J ⊓ L.U J'
    let V (s : M.ι) := (Ls s).U J ⊓ (Ls s).U J'
    have hV (s : M.ι) : V s = σ s ⁻¹ᵁ U := by
      change (Ls s).U J ⊓ (Ls s).U J' = _
      rw [charts, charts]
      rfl
    apply (sections U V hV).1
    funext s
    change pullOn s U (V s) (hV s).le (res inf_le_left (a J)) =
      pullOn s U (V s) (hV s).le (L.g J J' * res inf_le_right (a J'))
    have pull_restrict {A : Z.Opens} {B : (D s).Opens} (h : U ≤ A) (h' : V s ≤ B)
        (hB : B ≤ σ s ⁻¹ᵁ A) (b : Γ(Z, A)ˣ) :
        pullOn s U (V s) (hV s).le (res h b) = res h' (pullOn s A B hB b) := by
      apply Units.ext
      exact congrArg (fun q => q.hom b.val)
        (((σ s).map_appLE (hV s).le (homOfLE h).op).trans
          ((σ s).appLE_map hB (homOfLE h').op).symm)
    have transitions : pullOn s U (V s) (hV s).le (L.g J J') = (Ls s).g J J' := by
      let j := J PUnit.unit
      let k := J' PUnit.unit
      show pullOn s U (V s) (hV s).le
          (∏ _ : PUnit, res _ (pullU g _ (M.g j k)) ^ (1 : ℤ)) =
        ∏ _ : PUnit, res _ (pullU (σ s ≫ g) _ (M.g j k)) ^ (1 : ℤ)
      simp only [Fintype.prod_unique, zpow_one]
      apply Units.ext
      exact congrArg (fun q => q.hom (M.g j k).val)
        (Scheme.Hom.appLE_comp_appLE (σ s) g _ U (V s) _ (hV s).le)
    rw [map_mul, pull_restrict inf_le_left inf_le_left (charts s J).le,
      pull_restrict inf_le_right inf_le_right (charts s J').le, ha, ha, transitions]
    exact ht s J J'

end GlobalTheory.CompanionTheory.RigCover
