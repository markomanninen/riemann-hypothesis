module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionConstantMetricLine

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem intersection_snoc_constWeight : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (c : ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → II K ι P (e + 1) (Fin.snoc L (HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl))) = -c * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
  RootFieldNumerics.intersection_constant_metric_line

end GlobalTheory.CompanionTheory.Ar.Top
