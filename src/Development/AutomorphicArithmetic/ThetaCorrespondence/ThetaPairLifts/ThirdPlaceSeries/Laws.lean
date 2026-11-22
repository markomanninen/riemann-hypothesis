module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
variable {T : WDTie N A} (S : Reading T)
def LawsAlt : Prop :=
  ∀ (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), _root_.UpperTheory.One.M.RecLawsH (S i w hw).rc
end GlobalTheory.SplitRead
end
end
