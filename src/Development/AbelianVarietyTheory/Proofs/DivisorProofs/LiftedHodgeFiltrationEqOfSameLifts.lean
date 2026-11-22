module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowersStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTorsionLiftOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftFilEq

open GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing


set_option maxHeartbeats 1000000 in
theorem liftFil_le (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k)))
    [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left)
    (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁)
    (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂)
    (hA₁ : IsAbelianScheme A₁) (g : HdR A₀ → HdR A₀)
    (H₁ : ∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) (H₂ : ∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) :
    liftFil (epsDP k) h₁ ≤ liftFil (epsDP k) h₂ := by
  have P : AbelianDeRham := GlobalTheory.T.abelianScheme_firstDeRham_structure
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) A₁ hA₁
  have hA₀ : IsAbelianScheme A₀ := by
    have := hA₁.comm
    have hc : IsCommMonObj A₀ := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h₁.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h₁.2 T x y (pushPt h₁.1.w x) (pushPt h₁.1.w y) rfl rfl,
        ← h₁.2 T y x (pushPt h₁.1.w y) (pushPt h₁.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hc
            smooth := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 hA₁.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 hA₁.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₁.1 hA₁.geomConnected }
  have gA₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g₁).of_isPullback h₁.1 hg₁
  obtain ⟨C, _, φ, j, hφ, hic, e1⟩ := exists_const A₀
  have hBC := constMor_isBC P hA₀ gA₀ hφ hic e1
  have HC : Canonical (epsDP k) (TrivSqZeroExt.fstHom k k k).toRingHom :=
    canonical_of_abelianDeRham P (isDPNilpotent_squareZero _) (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl
  have step : ∀ x ∈ liftFil (epsDP k) h₁, ∃ y ∈ liftFil (epsDP k) h₁ ⊓ liftFil (epsDP k) h₂,
      ∃ z : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀, x = y + (DualNumber.eps : DualNumber k) • z := by
    intro x hx
    have ha := crysLo_mem_Fil P hA₁ hg₁ h₁ hx
    obtain ⟨d₁, hd₁, e₁⟩ := H₁ _ ha
    obtain ⟨d₂, hd₂, e₂⟩ := H₂ _ ha
    have e : d₁ = d₂ := crys_ext P hA₀ gA₀ fun c ↦ (e₁ c).trans (e₂ c).symm
    obtain ⟨z, hz⟩ := hBC.exists (crysHi x - g (crysLo x))
    have hd₁₂ : d₁ ∈ liftFil (epsDP k) h₂ := by rw [e]; exact hd₂
    refine ⟨d₁, ⟨hd₁, hd₁₂⟩, z, crys_ext P hA₀ gA₀ fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e₁, hz c, crys_constMor x c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hEq : liftFil (epsDP k) h₁ = liftFil (epsDP k) h₁ ⊓ liftFil (epsDP k) h₂ := by
    refine eq_of_le_of_le_add_eps ?_ inf_le_left step
    obtain ⟨N, hN⟩ := (HC g₁ A₀ A₁ i₁ h₁ hA₁ hg₁).2.1
    have c := HC.crysToDR_bijective h₁ hA₁ hg₁
    exact ⟨_, (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).symm.isCompl hN⟩
  exact fun x hx ↦ (hEq.le hx).2

theorem liftFil_eq : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k))) [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁) (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂), IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ g : HdR A₀ → HdR A₀, (∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) → (∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) → liftFil (epsDP k) h₁ = liftFil (epsDP k) h₂ := by
  intro k _ A₀ _ A₁ A₂ _ _ i₁ i₂ h₁ h₂ hA₁ hA₂ g H₁ H₂
  exact le_antisymm (liftFil_le k A₀ A₁ A₂ i₁ i₂ h₁ h₂ hA₁ g H₁ H₂)
    (liftFil_le k A₀ A₂ A₁ i₂ i₁ h₂ h₁ hA₂ g H₂ H₁)

end GlobalTheory.LiftFilEq
