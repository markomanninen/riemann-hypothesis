module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] (A : D ⥤ CommAlgCat.{0} R)

abbrev Co (k : ℕ) : Type 1 := CH.Cn (CH.modF A) k

def one0 : Co A 0 := fun s => (1 : A.obj (s.obj (Fin.last 0)))

theorem cech_d_one_zero : CH.d (CH.modF A) 0 (one0 A) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

section Res

variable {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) {U V : ObjectProperty C}

end Res

end GlobalTheory.CompanionTheory.ConeCech
