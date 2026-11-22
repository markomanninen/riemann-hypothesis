module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase

@[expose] public section

open GlobalTheory.AbLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SharpLift

theorem relAmple_of_closed_proper (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [IsProper B.hom] [Flat B.hom] (M : LB B.left) (hM : M.IsLB)
    (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀) (hg : Function.Surjective g)
    (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left)
    (hb : IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)))
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hA : RelAmple Y₀ N₀) : RelAmple B M := by
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine GlobalTheory.AmpleLocalBase.relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

theorem kTriv_of_localHom (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R]
    (π : R₁ →+* R) [IsLocalHom π] (B : Over (Sp R₁)) [GrpObj B] (hB : IsAbelianScheme B) (M : LB B.left) (hM : M.IsLB)
    (hA : RelAmple B M) (Y₀ : Over (Sp R)) [GrpObj Y₀] (b : Y₀.left ⟶ B.left) (hb : IsGrpPullback Y₀ B (spMap π) b)
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hK : KTriv Y₀ N₀) : KTriv B M := by
  obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb hiso hK (IsLocalRing.closedPoint R)
  have hcl : (spMap π) (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint R₁ := by
    exact IsLocalRing.comap_closedPoint π
  have htop : U = ⊤ := by
    rw [hcl] at hU
    exact top_le_iff.1 fun p _ => (IsLocalRing.specializes_closedPoint p).mem_open U.2 hU
  subst htop
  have hL := pull_isLB hM (pullback.fst B.hom (⊤ : (Sp R₁).Opens).ι)
  have hPB := isGrpPullback_pullback B (⊤ : (Sp R₁).Opens).ι
  have hAb : IsAbelianScheme ((Over.pullback (⊤ : (Sp R₁).Opens).ι).obj B) := by
    have := hB.comm
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hPB.1 hB.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hPB.1 hB.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hPB.1 hB.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro T
    refine ⟨⟨fun x y => Over.OverMorphism.ext (hPB.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hPB.2 T x y (pushPt hPB.1.w x) (pushPt hPB.1.w y) rfl rfl,
      ← hPB.2 T y x (pushPt hPB.1.w y) (pushPt hPB.1.w x) rfl rfl, _root_.mul_comm]
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ PUnit (fun _ => ⊤) B _ _ (by simp)
    (fun _ => isGrpPullback_pullback B _) _ _ hM (fun _ => hL) (fun _ => GlobalTheory.lbIso_refl hL) hB
    (fun _ => hAb) (fun _ => H)

end GlobalTheory.SharpLift
