module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsZmodOfFlatResolution
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_extendScalars_zmod_of_flat_resolution : ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q) (F : Shv (ZMod Q)) (T : Cx (ZMod Q)) [T.IsStrictlyGE 0], FlatS F → (∀ t, FlatS (T.X t)) → ∀ ε : sgl F ⟶ T, QuasiIso ε → QuasiIso ((GlobalTheory.EtC.ScalarExt.extCx (ZMod.castHom h (ZMod q))).map ε) := by
  first | exact @GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat | exact GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat | (intros; apply GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat <;> assumption)
