module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev tyOf (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Fin g → (E →+* ℂ) := fun j => relab c σ (e j).1

abbrev FamAt (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :=
  FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (tyOf c σ e)

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}

variable {F : FamAt Xo c σ e} {r : ℕ}

end GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies
