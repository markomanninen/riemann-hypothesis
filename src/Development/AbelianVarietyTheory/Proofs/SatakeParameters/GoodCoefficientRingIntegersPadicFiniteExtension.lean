module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem goodO_finExt_integers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  GlobalTheory.Pass.goodO_ringOfIntegers

end GlobalTheory.HTW.Rec
