module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjCechCompute
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistLeray

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

theorem nonempty_HTop_equiv (k : ℤ) (hn : 0 < n) :
    Nonempty (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) n ≃+
      (NegMon (n := n) k →₀ A)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hCech := nonempty_cechH_equiv_H_twist (𝒜 := grading A (m + 1))
    (fun j => MvPolynomial.X j) (fun j => X_mem j) iSup_stdOpen k (m + 1)
  obtain ⟨e⟩ := hCech
  exact ⟨e.symm.trans (cechHTopEquiv k m)⟩

theorem subsingleton_H (k : ℤ) {q : ℕ} (hq0 : 0 < q) (hqn : q ≠ n) :
    Subsingleton (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) q) := by
  have hCech := nonempty_cechH_equiv_H_twist (𝒜 := grading A n)
    (fun j => MvPolynomial.X j) (fun j => X_mem j) iSup_stdOpen k q
  obtain ⟨e⟩ := hCech
  have hSubsingleton :
      Subsingleton (cechH (twistAb (A := A) (n := n) k) (cover (A := A) (n := n)) q) := by
    rcases Nat.lt_or_gt_of_ne hqn with h | h
    · exact subsingleton_cechH_of_lt hq0 h
    · have hcard : Fintype.card (Fin (n + 1)) ≤ q := by simpa using h
      exact CechOrdered.subsingleton_cechH hcard hq0
  exact @Equiv.subsingleton _ _ e.symm.toEquiv hSubsingleton

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
