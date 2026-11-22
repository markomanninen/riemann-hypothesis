module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenPullComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRigidifiedLocallyTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivCond_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  intro S A _ N hA hN hR T t hloc Y φ y hY
  haveI := hA.comm
  letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
  let e : Over.mk y ≅ (Over.pullback t).obj A := Over.isoMk hY.isoPullback hY.isoPullback_hom_snd
  letI I : GrpObj (Over.mk y) := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  have hP : IsGrpPullback (Over.mk y) A t φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A t)).congr (Category.id_comp _)
      (by simp [e])
  have hA' : IsAbelianScheme (Over.mk y) := by
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hP.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hP.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hP.1 hA.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro U
    refine ⟨⟨fun x z => Over.OverMorphism.ext (hP.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hP.2 U x z (pushPt hP.1.w x) (pushPt hP.1.w z) rfl rfl,
      ← hP.2 U z x (pushPt hP.1.w z) (pushPt hP.1.w x) rfl rfl, _root_.mul_comm]
  haveI := hA'.comm
  obtain ⟨r, hr⟩ := hR
  have he : eSec (Over.mk y) ≫ φ = t ≫ eSec A := (cubeMapOf hP).e_comm
  have g := rigPullOf_isGen (G' := Over.mk y) (G := A) φ t he N r hr
  have hR' : Out.Rigidified (Over.mk y) (N.pull φ) := ⟨_, g⟩
  refine GlobalTheory.T.exists_generator_rigidified_locally_trivial T (Over.mk y) (N.pull φ) hA' (pull_isLB hN φ) hR' (fun τ => ?_)
  obtain ⟨V, hτ, hV⟩ := hloc τ
  refine ⟨V, hτ, ?_⟩
  have H : IsPullback ((y ⁻¹ᵁ V).ι ≫ φ) (y ∣_ V) A.hom (V.ι ≫ t) :=
    (isPullback_morphismRestrict y V).flip.paste_horiz hY
  exact (GlobalTheory.Mum.exists_gen_pull_pull_iff hN φ (y ⁻¹ᵁ V).ι).2 (hV _ _ _ H)

end GlobalTheory.TrivLocus
