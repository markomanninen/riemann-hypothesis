module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPsiGeneratingOnWholeSpectrum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi_generating_on_whole_spectrum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ ψ h, Nonempty (PsiOn (setPsi D ψ h) ⊤) := by
  first | exact @GlobalTheory.PsiTop.exists_setPsi_psiOn_top | exact GlobalTheory.PsiTop.exists_setPsi_psiOn_top | (intros; apply GlobalTheory.PsiTop.exists_setPsi_psiOn_top <;> assumption)
