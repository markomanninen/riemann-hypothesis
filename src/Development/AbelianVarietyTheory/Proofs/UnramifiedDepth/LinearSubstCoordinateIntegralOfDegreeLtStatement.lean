module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateIntegralOfDegreeLt
public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
public import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
public import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by
  first | exact @GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt | exact GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt | (intros; apply GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt <;> assumption)
