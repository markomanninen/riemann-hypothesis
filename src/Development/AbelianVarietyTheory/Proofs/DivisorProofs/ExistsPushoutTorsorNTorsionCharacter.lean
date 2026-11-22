module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDifferenceOneCochainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocOfIsSecDiff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAddOfIsSecDiffIsSecAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiEqOfTorsion

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem exists_pushout_torsor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (hn : (n : R) = 0) (hR : HasRoots A n) (b : Fn0 A) (hb : IsTorsChar n b) :
    ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
        chi n g D x = b D x := by
  have hSec := GlobalTheory.T.exists_pushoutTorsorSection_every_point R A n hR b hb
  let S : SecFam A := fun D _ _ x ↦ Classical.choose (hSec D x)
  have hS : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x) :=
    fun D _ _ x ↦ Classical.choose_spec (hSec D x)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionDifference_one_cochain R A n hR b hb S hS
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_sectionAddition_two_point_function R A n hR b hb S hS
  exact ⟨u, g, isCoc_of_isSecDiff R A n hR b hb S hS u hu,
    isAdd_of_isSecDiff_isSecAdd R A n hR b hb S hS u g hu hg,
    chi_eq_of_torsion R A n hn hR b hb S hS g hg⟩

end GlobalTheory.PtExt
