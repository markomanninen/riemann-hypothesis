module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrame
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterProductFormula
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDetCharacter_eq_prod_residue_goodBaseFrame : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ {A : Type} [CommGroup A] (t : Twist D A), t.Good → ∀ {κ : GA D T}, κ ∈ GfC T → Lev.finE T κ ∈ St B.F.βT → detChar T t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) := by
  exact @GlobalTheory.TwistDetStabAll.detChar_eq_prod_res
