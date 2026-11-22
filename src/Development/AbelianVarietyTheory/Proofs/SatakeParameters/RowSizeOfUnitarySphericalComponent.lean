module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowSizeClosing

theorem rowSize_of_unitarySphericalComponent :
    ∀ (D : D7), GlobalTheory.RowSatakeBound.UnitarySphericalComponent D.nd D.naut → GlobalTheory.RowCopy.RowSize D :=
  fun D h => by
    intro i σ hσ w hw hu α hα
    have hb := GlobalTheory.RowSatakeBound.rowSize_of_component D.nd D.naut h i σ hσ w hw hu α hα
    simpa only [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hb

end GlobalTheory.RowSizeClosing
