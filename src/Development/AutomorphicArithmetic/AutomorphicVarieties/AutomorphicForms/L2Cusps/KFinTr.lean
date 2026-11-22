module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact

@[expose] public section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem kFinTr_holds : KFinTr := by
  intro E _ _ _ a μ _ _ μ₁ _ hp v h
  have hi : Function.Injective (cmp hp) := (cmp hp).injective
  refine ⟨?_, ?_⟩
  · convert h.1 using 1
    ext k
    have e := cmpEquiv_holds E a μ μ₁ hp (finGL E a k) v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, e, hi.eq_iff, Fb.finEmb_eq]
  · have := h.2
    have hle : (Submodule.span ℂ (Set.range fun k : archCompact E a => archRepT μ₁ (k : archGroup E a) v)).map
        (cmp hp).toLinearMap ≤ Submodule.span ℂ
        (Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (cmp hp v)) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy⟩ := (Cm.grpEq E a).surjective (k : archGroup E a)
      have hu : y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := (Cm.grpEq_mem_archCompact y).1 (hy ▸ k.2)
      refine Submodule.subset_span ⟨⟨y.val, hu⟩, ?_⟩
      have ey : Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a) = y := Units.ext rfl
      change R (latticeGL E a) μ (infGL E a (Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a)))
        (cmp hp v) = cmp hp (archRepT μ₁ (k : archGroup E a) v)
      rw [ey, cmpEquiv_holds E a μ μ₁ hp (infGL E a y) v, ← Cm.infEmb_grpEq, hy, archRepT_apply,
        retract_infEmb]
    have := Submodule.finiteDimensional_of_le hle
    exact (Submodule.equivMapOfInjective (cmp hp).toLinearMap hi _).symm.finiteDimensional

end UpperTheory.V.KernelIndexFullLattice
