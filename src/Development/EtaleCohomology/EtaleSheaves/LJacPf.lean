module

public import Development.EtaleCohomology.EtaleSheaves.HensIdemCut

@[expose] public section

namespace LateralTheory.E.LJacPf

theorem LJac_of : LateralTheory.E.HensIdemCut.LJac := by
  intro A _ I hH B _ φ hφ
  letI := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  have hI : I ≤ Ideal.jacobson ⊥ := by simpa only [Ideal.jacobson_bot] using hH.jac
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro m ⟨-, hm⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (m.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φ hφ m
  refine hI.trans ?_
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, this⟩

end LateralTheory.E.LJacPf
