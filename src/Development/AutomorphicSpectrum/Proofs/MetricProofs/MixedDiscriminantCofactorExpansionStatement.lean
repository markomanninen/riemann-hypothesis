module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansion
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_cofactor_expansion : ∀ (d : ℕ), (∀ (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ), ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) = ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s))) ∧ ∃ Λ : MultilinearMap (RingHom.id ℂ) (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ, (∀ Bm, Λ Bm = mdisc Bm) ∧ ∀ (π : Equiv.Perm (Fin d)) Bm, Λ (Bm ∘ π) = Λ Bm := by
  have h := PositivityTheory.Xgp.t_fib_mdisc
  exact h
