module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PointsSumsEqProducts
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIsoStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_oAct_rosatiConj : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))), ∃ oa : T.pol.OAct (𝓞 E), oa.act = T.t.act.act ∧ RosatiConj T.pol oa := by
  intro hL E _ _ _ _ H hs K _ _ T
  have : IsCommMonObj T.pol.A := T.pol.isAb.comm
  obtain ⟨ra, hra⟩ := (ringAct_iff_oAct (𝓞 E) (Sp (𝓞 K)) T.pol.A).2 T.t.act
  have hlam : ∀ a : 𝓞 E, LamEq T.pol.L (ra.act a) (𝟙 T.pol.A) T.pol.L (𝟙 T.pol.A) (ra.act (star a)) := by
    intro a
    rw [hra, hs]
    have h := T.t.adj a
    simpa [LamEq] using h
  refine ⟨⟨ra, fun a => (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hL.globalFns _ T.pol _ _ (ra.hom a) (ra.hom _)).2 (hlam a)⟩,
    hra, ?_⟩
  intro a Tb k x z c hk hx hz
  have hp : ∀ (n : ℕ) (p : Tb ⟶ T.pol.A), pnsmulPt n p = p ^ n := by
    intro n p
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have hu : toUnit Tb ≫ η[T.pol.A] = (1 : Tb ⟶ T.pol.A) := rfl
  rw [hp, hu] at hx hz
  have := GlobalTheory.T.commutatorPairings_eq_of_cubeLBPairingIso hL (𝓞 K) T.pol T.pol T.pol T.pol (ra.act a) (𝟙 _) (𝟙 _) (ra.act (star a)) (ra.hom a)
    inferInstance inferInstance (ra.hom _) (hlam a) Tb k x z c hk hx hz
  simpa using this

end GlobalTheory.LamF
