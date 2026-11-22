module

public import Formalism.GradedWeylDivisibility.StatementD

@[expose] public section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem ldtwist_map_rowAct {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K) :
    map φ (rowAct K g F) = rowAct L (g.map φ) (map φ F) := by
  induction F using MvPolynomial.induction_on
  · rename_i a
    simp [rowAct]
  · rename_i p q hp hq
    simp only [map_add (f := _), hp, hq]
  · rename_i p v hp
    simp only [map_mul, hp]
    congr 1
    simp [rowAct, Matrix.map_apply]

end Formalism.GradedWeylDivisibility
