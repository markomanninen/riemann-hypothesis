module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanDarbouxCoordsOneParamOrbitSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ X, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  first | exact @GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left | exact GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left | (intros; apply GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left <;> assumption)
