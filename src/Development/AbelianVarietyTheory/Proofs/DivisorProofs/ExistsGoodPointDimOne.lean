module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCobOneOfIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LePreimageOfClosedPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupScheStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.TorusTateLie
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointMap

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}
  (α : P.A.A ⟶ P'.A.A) [IsMonHom α]

section Lattices

variable [Algebra ℤ_[p] C]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

end Lattices

variable [IsAlgClosed C] [CharZero C]

theorem pairV_mapV [Algebra ℤ_[p] C] (x : P.V) (y : P'.V) :
    P'.pairV (mapV P P' α x) y = P.pairV x (adjV P P' α y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx']
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
    | tmul d t => exact congrArg (· • (c * d)) (pairT_mapT P P' α s t)

theorem weil_adjT (he : P'.eps = P.eps) (t : P'.T) {n : ℕ} {z : ChTor.Pts P.A.A} (hz : z ^ p ^ n = 1) :
    weil P'.A (p ^ n) (z ≫ α) (t.lev n) = weil P.A (p ^ n) z ((adjT P P' α t).lev n) := by
  obtain ⟨s, rfl⟩ := (tate_free_of_card p _ _ P.card_torsion).2.1 n z hz
  rw [← pow_pairT P.A P.eps, ← pairT_mapT, ← he, pow_pairT, lev_mapT]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  (β : P.Gt ⟶ P'.Gt) [IsMonHom β] (he : P'.eps = P.eps) (hβ : ∀ x, P'.toA (x ≫ β) = P.toA x ≫ α)

include he hβ

theorem weilChar_adjT (t : P'.T) (n : ℕ) : (P.weilChar (adjT P P' α t)).χ n =
    ExtensionTorsion.torsionHom β (p ^ n) ≫ (P'.weilChar t).χ n := P.char_ext fun w => by
  rw [← Category.assoc, P.isWeilChar_weilChar, P'.isWeilChar_weilChar, Category.assoc,
    ExtensionTorsion.torsionHom_ι, ← Category.assoc, hβ, weil_adjT α he t (P.toA_pow w)]

variable [Algebra ℤ_[p] O]

theorem al₀_adjT (t : P'.T) (x : LieG P.Gt) :
    (P.al₀ (adjT P P' α t)).1 x = (P'.al₀ t).1 (lieMap β x) := by
  refine HodgeTateImage.eq_of_forall (p := p) fun n => ?_
  have hR := HodgeTateImage.pow_quot (O := O) (p := p) n
  have h1 := isAl_dlogTv (P.weilChar (adjT P P' α t)) n _ hR x _ (HodgeTateImage.lift_ι hR x)
  have h2 := isAl_dlogTv (P'.weilChar t) n _ hR (lieMap β x)
    (HodgeTateImage.lift hR x ≫ ExtensionTorsion.torsionHom β (p ^ n)) (by
      rw [Category.assoc, ExtensionTorsion.torsionHom_ι, ← Category.assoc, HodgeTateImage.lift_ι]
      exact Category.assoc _ _ _)
  rw [Category.assoc, ← weilChar_adjT α β he hβ, h1] at h2
  change algebraMap O _ ((dlogTv (P.weilChar (adjT P P' α t))).1 x) =
    algebraMap O _ ((dlogTv (P'.weilChar t)).1 (lieMap β x))
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd h2

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem mapV_bLie (x : LieG P.Gt) : mapV P P' α (P.bLie x) = P'.bLie (lieMap β x) :=
  P'.eq_of_pairV fun t => by
    rw [pairV_mapV, adjV_tmul, Point.pairV_bLie, Point.pairV_bLie, al₀_adjT α β he hβ]

end General

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type}
  [CommRing R] (j : R →+* O) {B B' B'' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ) (o'' : B''.OAct Λ)

theorem homT_act (a : Λ) [IsMonHom (o.act a)] : homT hv ε j o o (o.act a) = (goodPoint hv ε j B o).actT a :=
  LinearMap.ext fun t => Tate.ext fun n => congrArg (t.lev n ≫ ·) (goodPoint_oA hv ε j o a).symm

theorem homT_id : homT hv ε j o o (𝟙 B.A) = LinearMap.id :=
  LinearMap.ext fun t => Tate.ext fun n =>
    (congrArg (t.lev n ≫ ·) ((congrArg _ ((Over.pullback _).map_id _)).trans ((Over.pullback _).map_id _))).trans
      (Category.comp_id _)

section Linear

variable {f : B.A ⟶ B'.A} [IsMonHom f]

variable [Algebra ℤ_[p] C]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

end Linear

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem toG_goodPoint (x : specO O O ⟶ (goodPoint hv ε j B o).Gt) : (goodPoint hv ε j B o).toG x = x :=
  (goodPoint hv ε j B o).hom_ext_red fun m => (goodPoint hv ε j B o).red_toG x m

theorem toA_homO (f : B.A ⟶ B'.A) (x : specO O O ⟶ (goodPoint hv ε j B o).Gt) :
    (goodPoint hv ε j B' o').toA (x ≫ homO hv ε j o o' f) = (goodPoint hv ε j B o).toA x ≫ homC hv ε j o o' f := by
  have h1 := ((goodPoint hv ε j B o).eq_toA_iff x _).1 rfl
  have h2 : (homC hv ε j o o' f).left ≫ (goodPoint hv ε j B' o').gen =
      (goodPoint hv ε j B o).gen ≫ (homO hv ε j o o' f).left := pullback.lift_fst _ _ _
  rw [toG_goodPoint] at h1
  symm
  rw [Point.eq_toA_iff, toG_goodPoint, Over.comp_left, Category.assoc, h2]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (homO hv ε j o o' f).left) h1).trans (Category.assoc _ _ _))

variable [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem homV_bLie (f : B.A ⟶ B'.A) [IsMonHom f] (x : LieG (goodPoint hv ε j B o).Gt) :
    homV hv ε j o o' f ((goodPoint hv ε j B o).bLie x) = (goodPoint hv ε j B' o').bLie (homLie hv ε j o o' f x) :=
  mapV_bLie _ (homO hv ε j o o' f) rfl (toA_homO hv ε j o o' f) x

variable {f : B.A ⟶ B'.A} [IsMonHom f]


end Good

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] {ℓ : ℕ} [Fact ℓ.Prime]
  {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O)
  (ε : Eps ℓ C) (i : K →+* C) {T T' : PAT H (Sp (𝓞 K))} {f g : T.t.G ⟶ T'.t.G}
  (hf : Serre.IsLinearHom T.t.act T'.t.act f) (hg : Serre.IsLinearHom T.t.act T'.t.act g)

variable [Algebra ℤ_[ℓ] C]

variable [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C]

variable [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [IsAlgClosed C] [CharZero C]

theorem patV_bLie : letI := H.starRing
    ∀ x, patV hv ε i hf ((patPoint hv ε i T).bLie x) = (patPoint hv ε i T').bLie (patLie hv ε i hf x) :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homV_bLie (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

end Triples

end GlobalTheory.PointMap
