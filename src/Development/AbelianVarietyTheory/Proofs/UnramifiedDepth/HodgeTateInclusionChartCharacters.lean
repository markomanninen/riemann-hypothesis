module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.TowerZeroSurjective
public import ReciprocityTheory.DualLattices.LinPairStatement
public import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapPderiv
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroupStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearDataOfSplitFormalGroupExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariantStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsHodgeTateDatumPolarisedAbelianCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearDataHodgeTateInclusionStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawJacobianExtensionChangeCoeffStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilChartOfIsChartJStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentChartsStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUnique
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem eq_intCast_of_conj {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {g : ℕ}
    (ρ : (ℤ_[p] ⊗[ℤ] ℤ) →+* Matrix (Fin g) (Fin g) O) (S M : Matrix (Fin g) (Fin g) O) (hS : IsUnit S) (a : ℤ)
    (h : M * S = S * ρ (1 ⊗ₜ[ℤ] a)) : M = (a : Matrix (Fin g) (Fin g) O) := by
  have h1 : ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) = ((a : ℤ) : ℤ_[p] ⊗[ℤ] ℤ) := by
    rw [← Algebra.TensorProduct.includeRight_apply]; simp
  rw [h1, map_intCast] at h
  obtain ⟨u, rfl⟩ := hS
  rw [← (Int.cast_commute a (u : Matrix (Fin g) (Fin g) O)).eq] at h
  exact (Units.mul_left_inj u).mp h

private theorem mul_intCast_eq {O : Type} [CommRing O] {m n : ℕ} (M : Matrix (Fin m) (Fin n) O) (a : ℤ) :
    M * (a : Matrix (Fin n) (Fin n) O) = (a : Matrix (Fin m) (Fin m) O) * M := by
  ext i j
  simp [Matrix.mul_apply, Matrix.intCast_apply, mul_comm]

theorem hodgeTate_inclusion_chart : ∀ (p : ℕ) [Fact p.Prime], HTFSt p := by
  intro p _ T _ _ _ _ _ _ hp G _ _ D A x d F xx hC C _ _ _ v O _ _ hv _ _ iota hiota
  obtain ⟨hL1, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨-, -, -, -, -, -, hcube, -⟩ := hL1
  letI : Algebra ℤ_[p] O := ((GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).1).some
  have hFH : FH p (F.mapF iota) := by
    have h := GlobalTheory.FormalTorsion.fhSt p
    unfold FHSt at h
    unfold FH
    intro m
    obtain ⟨h1, h2, -, h4⟩ := h T hp G D A x d F xx hC C v O hv iota hiota m
    exact ⟨h1, h2, h4⟩
  obtain ⟨X, hX, -⟩ := GlobalTheory.ChF.nilChart_of_isChartJ T G x.1 d F xx hC
  obtain ⟨FB, xB, hxB⟩ := GlobalTheory.ChF.exists_nilChart T D.toPre.P.A D.toPre.P.g D.toPre.P.5
  obtain ⟨r, J, Q, hEx, -⟩ := GlobalTheory.unif_extSer_equivariant T (IsLocalRing.maximalIdeal T) D A G x d D.toPre.P.g F FB X xB hX hxB
  obtain ⟨o, ho⟩ := GlobalTheory.exists_oAct_int hcube (Spec (CommRingCat.of T)) D.toPre.P
  have hα : ∀ a : ℤ, ∃ φ, Reads xB xB (o.act a) φ := fun a =>
    GlobalTheory.ChF.exists_reads T D.toPre.P.A D.toPre.P.A D.toPre.P.g D.toPre.P.g FB.F FB.F xB xB hxB hxB (o.act a)
      (by
        rw [ho a]
        refine ⟨?_, ?_⟩
        · simp only [GrpObj.comp_zpow, Category.comp_id, MonObj.one_eq_one, _root_.one_zpow]
        · simp only [GrpObj.comp_zpow, Category.comp_id, MonObj.mul_eq_mul, mul_zpow,
            MonObj.comp_mul, tensorHom_fst, tensorHom_snd])
  choose α hα using hα
  obtain ⟨hmapF, -, hmapEx⟩ := GlobalTheory.ChF.changeCoeff_law_lin_extSer T O iota
  obtain ⟨F', hF'⟩ := hmapF d F
  obtain ⟨FB', hFB'⟩ := hmapF D.toPre.P.g FB
  obtain ⟨cp, hUp, H, S, hP, hPL, hS, hSa, hSu⟩ :=
    GlobalTheory.ChF.exists_htd_characters_base p C v O hv T iota D.toPre.P D.toPre.P.g rfl ℤ o FB xB hxB α hα
  have hαB : ∀ a : ℤ, lin (fun j => MvPowerSeries.map iota (α a j)) =
      (a : Matrix (Fin D.toPre.P.g) (Fin D.toPre.P.g) O) := fun a =>
    eq_intCast_of_conj H.ρL S _ hS a (hSa a)
  obtain ⟨cp', hUp', H', B, m, u, hu, hLin⟩ :=
    GlobalTheory.ChF.exists_linDat_of_extSer p C v O hv ℤ d D.toPre.P.g r F' FB' (fun j => MvPowerSeries.map iota (J j))
      (fun j => MvPowerSeries.map iota (Q j)) (by rw [hF', hFB']; exact hmapEx d D.toPre.P.g r F FB J Q hEx)
      (by rw [hF']; exact hFH) (Int.castRingHom _) (Int.castRingHom _)
      (fun a j => MvPowerSeries.map iota (α a j))
      (fun a => by rw [hαB a, eq_intCast]; exact mul_intCast_eq _ a)
      (fun a => by
        have e : ((a : Matrix (Fin r) (Fin r) ℤ)).map (Int.castRingHom O) = (a : Matrix (Fin r) (Fin r) O) :=
          map_intCast (Int.castRingHom O).mapMatrix a
        rw [eq_intCast, eq_intCast, e]
        exact (mul_intCast_eq _ a).symm)
      ⟨cp, hUp, H, S, hP, hPL, hS, hSa, by rw [hFB']; exact hSu⟩
  refine ⟨m, u, fun k => hF' ▸ hu k, ?_⟩
  intro c hc f
  exact GlobalTheory.ChF.linDat_hodgeTate_inclusion p C v O hv ℤ cp' hUp' D.toPre.P.g H' d r m _ B (Int.castRingHom _) (Int.castRingHom _)
    (fun k => dl (u k)) hLin c hc f

end GlobalTheory.ChF
