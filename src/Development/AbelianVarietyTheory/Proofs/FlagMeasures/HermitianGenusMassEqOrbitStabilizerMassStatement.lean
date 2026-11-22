module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsFullLattice K L → ENNReal.ofReal (mass h L) = orbMass (isom h) (genus h L) ∧ 0 < mass h L ∧ Stable (isom h) (genus h L) ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → Finite (MulAction.stabilizer (isom h) M)) ∧ ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : isom h) M, N (g • M) = N M) → ∑ M ∈ s, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M = orbSum (isom h) (genus h L) N := by
  first
  | exact @GlobalTheory.Mass.GenusOrb.main
  | intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
    obtain ⟨a, b, c, d, e⟩ := GlobalTheory.Mass.GenusOrb.main K V h hK hs hp L hL.toIsLattice
    exact ⟨a, b, c, fun M hM => d M hM.toIsLattice, e⟩
