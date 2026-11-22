module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Mathlib
public import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfTrivialInteger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentativesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformTorusVanishing
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeEsymmLMulSchur
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewformStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescriptionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescriptionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralPropertiesStatement
public import GroundTheory.AutomorphicForms.HaarSK
public import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
public import GroundTheory.LocalFields.LocalZetaEpsilon
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalFunctionalEquationH1
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistenceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductorStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacterStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalTypeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvaluesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecayStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficientsStatement
public import GroundTheory.AutomorphicForms.CompactAbelianCharacters
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero

@[expose] public section

private theorem norm_sq_of_scaled (k p : ℕ) (hk : 3 ≤ k) (hp : 2 ≤ p) (x : ℂ)
    (h : ‖x * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = (p : ℝ)) : ‖x‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hr : (0 : ℝ) < (p : ℝ) ^ (1 - (k : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow] at h
  have hr2 : ((p : ℝ) ^ (1 - (k : ℝ) / 2)) ^ 2 = (p : ℝ) ^ (2 - (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have he : (((k - 1 : ℕ) : ℝ)) + (2 - (k : ℝ)) = 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hkey : (p : ℝ) ^ (k - 1) * (p : ℝ) ^ (2 - (k : ℝ)) = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0, he, Real.rpow_one]
  have hne : (p : ℝ) ^ (2 - (k : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  rw [hr2] at h
  exact mul_right_cancel₀ hne (h.trans hkey.symm)

theorem UpperTheory.V.Z.Sym.Unl.badAbs :
    UpperTheory.V.Z.Sym.Unl.BadAbs := by
  intro k N _ hk χ hχ g p hp hpN
  have b0 : Ad3.R.B0 := @GlobalTheory.T.global_rankin_selberg_basic_facts
  have c0 : Ad3.R.C0 := @GlobalTheory.T.hecke_coset_representatives
  have c1 : Ad3.R.C1 := @GlobalTheory.T.congruence_subgroup_coset_decomposition
  have u2 : Ad3.R.U2 := @GlobalTheory.T.unramified_whittaker_newform
  have g0 : Ad3.R.G0 := @GlobalTheory.T.fundamental_domain_invariance_of_description (@GlobalTheory.T.fundamental_domain_description)
  have g1 : Ad3.R.G1 := @GlobalTheory.T.central_character_integral_properties (@GlobalTheory.T.fundamental_domain_integral_central_invariance)
  have f0 : Ad3.R.F0 := @GlobalTheory.T.newform_lift_existence b0
  have f0b : Ad3.R.F0b := @GlobalTheory.T.newform_lift_conductor b0
  have f1 : Ad3.R.F1 := @GlobalTheory.T.newform_lift_level b0
  have f1b : Ad3.R.AutomorphicLevelEquivariance := @GlobalTheory.T.newform_lift_level_character b0
  have f2 : Ad3.R.F2 := @GlobalTheory.T.newform_lift_whittaker_expansion
  have f3a : Ad3.R.HeckeSumLocalTranslates := @GlobalTheory.T.newform_lift_local_type b0
  have f3 : Ad3.R.F3 := @GlobalTheory.T.newform_lift_hecke_eigenvalues b0 c0 c1 f0b f1 f1b f3a
  have f5 : Ad3.R.F5 := @GlobalTheory.T.newform_lift_rapid_decay b0
  have f4 : Ad3.R.F4 := @GlobalTheory.T.newform_lift_fourier_coefficients b0 c1 u2 g0 g1 f0b f1 f2 f3 f5
  obtain ⟨hform, heig⟩ := Ad3P.sEig k N hk χ g
  obtain ⟨ω, hω⟩ := f0 N χ
  obtain ⟨-, φ, hφ⟩ := f1 k N χ _ _ hform g.one ω hω
  obtain ⟨v, rfl⟩ := b0.2.2.1 p hp
  have h := f4 k N hk χ hχ _ _ hform heig ω φ hω hφ v hpN
  exact norm_sq_of_scaled k _ hk hp.two_le _ h
