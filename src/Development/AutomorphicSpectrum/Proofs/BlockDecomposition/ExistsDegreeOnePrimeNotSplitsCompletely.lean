module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity

@[expose] public section

open NumberField IsDedekindDomain GroundTheory.Global

namespace GlobalTheory.CompanionTheory.Density


open Filter Topology Set in
theorem exists_degreeOnePrime_not_splitsCompletely :
    ∀ (L F M : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], 1 < Module.finrank F M →
      ∀ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite →
        ∃ v ∈ degreeOnePrimes L F, v ∉ B ∧ ¬ SplitsCompletely M v := by
  intro L F M _ _ _ _ _ _ _ _ _ hdeg B hB
  by_contra hcon
  push Not at hcon
  have hfin : (degreeOnePrimes L F \ ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩ degreeOnePrimes L F)).Finite := by
    apply hB.subset
    intro v hv
    by_contra hvB
    exact hv.2 ⟨hcon v hv.1 hvB, hv.1⟩
  have hinter : ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩
      degreeOnePrimes L F).HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_iff_of_subset_of_isBoundedUnder
      Set.inter_subset_right
      (GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_of_finite hfin) 1).mpr
      (GroundTheory.Global.hasDirichletDensity_degreeOnePrimes (K := L) (L := F))
  have hsplit : {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}.HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_inter_degreeOnePrimes_iff
      (K := L) _ 1).mp hinter
  have hSd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely (K := F) (L := M)
  have heq : (1 : ℝ) = 1 / Module.finrank F M :=
    hsplit.dirichletDensity_eq.symm.trans hSd.dirichletDensity_eq
  have h2 : 2 ≤ Module.finrank F M := hdeg
  have hfr : (2 : ℝ) ≤ Module.finrank F M := by exact_mod_cast h2
  have hq : (1 : ℝ) / Module.finrank F M ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfr
  linarith

end GlobalTheory.CompanionTheory.Density
