module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.LeafLevelPf
open LateralTheory.CohomologicalPurity.TubeCut

variable {J : Type} [SmallCategory J]

theorem elt_eqToHom {F : J ⥤ Type} {a b : F.Elements} (h : a = b) :
    (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by subst h; rfl

theorem chn_eq (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (x : ((hoc D).obj n).obj U) :
    (inj D n (chn x ⋙ Functor.Elements.π _)).app U (chn x |>.obj 0).val = x := by
  change mkChn (F := D.flip.obj U) _ _ _ = chn x
  fapply CategoryTheory.Functor.ext
  · intro i
    let f := (chn x).map (homOfLE (Fin.zero_le i))
    refine Functor.Elements.ext _ _ (by rfl) ?_
    change (D.flip.obj U).map (𝟙 ((chn x).obj i).obj)
      ((D.flip.obj U).map f.hom ((chn x).obj 0).val) = ((chn x).obj i).val
    rw [(D.flip.obj U).map_id]
    exact f.map_val
  · intro i k g
    apply Functor.Elements.hom_ext
    rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom]
    erw [elt_eqToHom, elt_eqToHom]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

theorem bij (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) :
    Function.Bijective (Cofan.mk (((hoc D).obj n).obj U) (fun σ => ((evaluation _ _).obj U).map (inj D n σ)) :
      Cofan fun σ : Fin (n.unop.len + 1) ⥤ J => ((evaluation _ _).obj U).obj (D.obj (σ.obj 0))).cofanTypes.fromSigma := by
  constructor
  · rintro ⟨σ, a⟩ ⟨σ', a'⟩ h
    change (inj D n σ).app U a = (inj D n σ').app U a' at h
    have e : σ = σ' := congrArg (fun F => F ⋙ Functor.Elements.π (D.flip.obj U)) h
    subst e
    have h2 := congrArg (fun F : Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements => F.obj 0) h
    have h3 : (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a =
        (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a' := by
      change (D.flip.obj U).elementsMk (σ.obj 0) _ = (D.flip.obj U).elementsMk (σ.obj 0) _ at h2
      injection h2
    have hid : ∀ b : ((evaluation _ _).obj U).obj (D.obj (σ.obj 0)), (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U b = b := by
      intro b
      have : (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := rfl
      rw [this, σ.map_id, D.map_id]; rfl
    rw [hid, hid] at h3
    subst h3; rfl
  · intro x
    exact ⟨⟨chn x ⋙ Functor.Elements.π _, (chn x |>.obj 0).val⟩, chn_eq D n U x⟩

theorem LeafLevel_of : LeafLevel := by
  intro J _ D n
  refine ⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ _).symm ?_
  exact Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2 (bij D n U))

end LateralTheory.CohomologicalPurity.LeafLevelPf
