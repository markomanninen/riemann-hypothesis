module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

@[expose] public section

namespace GlobalTheory

theorem exists_valuationSubring_complex_comap_val_eq (F : IntermediateField ℚ ℂ)
    (U : ValuationSubring F) (p : ℕ) (hp : (p : F) ∈ U.nonunits) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  obtain ⟨W, hW⟩ : ∃ W : ValuationSubring ℂ, W.comap (algebraMap F ℂ) = U :=
    exists_valuationSubring_comap_eq U _
  refine ⟨W, ?_, hW⟩
  rw [ValuationSubring.mem_nonunits_iff_or] at hp ⊢
  rcases hp with h | h
  · left
    simpa using congrArg (algebraMap F ℂ) h
  · right
    rw [← hW, ValuationSubring.mem_comap] at h
    simpa using h

end GlobalTheory
