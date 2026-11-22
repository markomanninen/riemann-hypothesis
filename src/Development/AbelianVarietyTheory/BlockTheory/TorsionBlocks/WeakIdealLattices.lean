module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {l : ℕ} [Fact l.Prime]

def cZero (l : ℕ) (m : ℕ) (U : Finset ℤ) : ℕ := 2 + ∑ u ∈ U, (m + padicValInt l u)

theorem finiteDimensional_Ks (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  haveI : Finite {x : Om l | x ^ (l ^ s) = 1} := by
    refine Set.Finite.to_subtype ((Polynomial.nthRoots (l ^ s) (1 : Om l)).toFinset.finite_toSet.subset ?_)
    intro x hx
    simpa [Polynomial.mem_nthRoots hpos] using hx
  haveI : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

def KsFin (K : FinExt l) (s : ℕ) : FinExt l := ⟨Ks K s, finiteDimensional_Ks K s⟩

section Ring

variable {P : LocPrime l} (AI : LocAinf l P)

end Ring

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  {R : Type} [CommRing R] [Algebra O R]

end Generic

section Hyp

variable {K LL : FinExt l}

variable {P : LocPrime l} (AI : LocAinf l P)


end Hyp

end GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants
