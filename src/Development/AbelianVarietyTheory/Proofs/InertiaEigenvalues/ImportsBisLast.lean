module

public import Mathlib
public import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisationsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DesignUnconditional

theorem main : ∀ D : D7, GlobalTheory.CoefDuty.TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D :=
  GlobalTheory.T.designConditionAll_of_cheb_of_takenAll (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.mp GlobalTheory.Published.chebotarevDegreeOne')

end GlobalTheory.DesignUnconditional
