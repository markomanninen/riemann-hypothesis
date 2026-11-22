module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeClosedPoint
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime geoNum divSupp multAt)

theorem linForm_single {F : Type} [Field F] {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : F)) = X i := by
  simp [linForm, Pi.single_apply]

end ObjectsChow

end GroundTheory.Heights₂.Heights
