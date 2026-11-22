module

public import Mathlib

@[expose] public section

namespace GlobalTheory.UnitLemma

def valsAt {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ} (e : Fin r → ι) :
    G →* Multiplicative (Fin r → ℤ) :=
  (MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))

theorem valsAt_apply {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ}
    (e : Fin r → ι) (x : G) (j : Fin r) :
    Multiplicative.toAdd (valsAt w e x) j = Multiplicative.toAdd (w (e j) x) := rfl

end GlobalTheory.UnitLemma
