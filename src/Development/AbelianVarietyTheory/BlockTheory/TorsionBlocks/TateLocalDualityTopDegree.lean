module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

def intSub (LL : FinExt l) : Submodule ↥(OL LL) ↥LL.1 :=
  LinearMap.range (Algebra.linearMap ↥(OL LL) ↥LL.1)

theorem norm_chi_le_one (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) :
    ‖(((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc (g : GQ l) 0 1 (by simp)
  rw [P.PD_χ]
  have h1 : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ≤ 1 := by simpa using ha
  have h2 : ‖(a : ℚ_[l])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := l) (a : ℤ)
  have h3 := IsUltrametricDist.norm_add_le_max
    (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) (a : ℚ_[l])
  rw [sub_add_cancel] at h3
  exact h3.trans (max_le h1 h2)

def chiInt (P : LocPrime l) (K : FinExt l) : ↥(GK K) →* ℤ_[l] where
  toFun g := ⟨(((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]), norm_chi_le_one P K g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    change (((P.PD K).χ (g * h) : ℚ_[l]ˣ) : ℚ_[l]) =
      (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) * (((P.PD K).χ h : ℚ_[l]ˣ) : ℚ_[l])
    rw [map_mul, Units.val_mul])

end GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo
