module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantLeviElement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_invariant_levi_element : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
  PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
  ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g a hg Φ
  obtain ⟨-, -, -, ⟨-, hχ⟩, -, -, -, hW⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hg' : mat g = blk4 (a' : Matrix (Fin n) (Fin n) (AE D)) 0 0
      (adj ((a'⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D))) := hg
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D : D.host.E →* AE D) (Matrix.GeneralLinearGroup.det a) :=
    Units.ext (by exact (RingHom.map_det (incA D) a.1).symm)
  have hχ1 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact hχ _
  have habs : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact absE_inclR _
  have hc : ∀ x, (ω g Φ).1 x = Φ.1 (x * (a' : Matrix (Fin n) (Fin n) (AE D))) := by
    intro x
    rw [hW.levi g a' hg' Φ x, hχ1, habs]
    simp [npow]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * (a : Matrix (Fin n) (Fin n) D.host.E)).map (incA D)) := by
    intro ξ
    rw [hc, Matrix.map_mul]
    rfl
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * (a : Matrix (Fin n) (Fin n) D.host.E)
      invFun := fun ξ => ξ * ((a⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      left_inv := fun ξ => by simp [Matrix.mul_assoc]
      right_inv := fun ξ => by simp [Matrix.mul_assoc] }
  rw [tsum_congr hterm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))
