module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpTie

theorem not_dvd_discr_host (D : D7) {l : ℕ} (hl : l.Prime) (hS : l ∉ Formalism.MainNotions.JumpSetsAlt.excSet D) :
    ¬ ((l : ℕ) : ℤ) ∣ NumberField.discr D.host.E :=
  UpperTheory.ExcSet.not_dvd_discr D hl hS

end GlobalTheory.ExpTie
