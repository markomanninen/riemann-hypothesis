module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPointStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GtAddIotaSubExist
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPointStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaParameterOfThetaParameterMulDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCarries

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_parAt : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a : u.PtC), ∃ g, u.ParAt S.N a g := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l a
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h1 : 2 ≤ ρ.n ^ ρ.k := le_trans ρ.n_prime.two_le
      (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    nlinarith
  haveI : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  obtain ⟨k, hk, hint⟩ := GlobalTheory.T.theta_test_power_integral hL o Ω S ρ p y₀ u a
  obtain ⟨a₁, ⟨c, hc, hca⟩, hpow⟩ := GlobalTheory.T.exists_integral_nthRoot_testModel_point hL o Ω S ρ p y₀ u (a ^ k) k hk hint
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.exists_torusExtensionPoint_of_integralModelPoint hL o Ω S ρ p y₀ u c hc
  have hpar := (GlobalTheory.T.torusCoord_unit_and_section_eq_expansion hL o Ω S ρ p y₀ u c g₁ a₁ hc hca hg₁).2
  have hNk : 1 ≤ S.N * k := Nat.mul_pos (by omega) hk
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.N * k) hNk
  haveI : IsMonHom u.U.gen.hom := u.U.gen_hom
  have hk' : (a₁ ≫ u.U.gen.hom) ^ k = (a ≫ u.U.gen.hom) ^ k := by
    rw [← MonObj.pow_comp, ← MonObj.pow_comp, hpow]
  have hx : ((a ≫ u.U.gen.hom) * (a₁ ≫ u.U.gen.hom)⁻¹) ^ (S.N * k) = 1 := by
    rw [mul_comm S.N k, pow_mul, mul_pow, inv_pow, hk', mul_inv_cancel, one_pow]
  obtain ⟨pk, hpk⟩ := hsurj _ hx
  obtain ⟨g, hg⟩ := (gt_add_iota_sub_exist hL o Ω S ρ p y₀ u).1 pk.g g₁
  refine ⟨g, GlobalTheory.T.thetaParameter_of_thetaParameter_mul_degree hL o Ω S ρ p y₀ u l S.N k a g hN hk ?_⟩
  exact ParTranslate.parAt_translate hL o Ω S ρ p y₀ u (S.N * k) pk _ a₁ a g₁ g hNk
    ((hf pk _).2 hpk.symm) (by rw [inv_mul_cancel_right]) hg (hpar _ hNk)

end GlobalTheory.ZH
