module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumArcLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.CuspFamilyCompare

section Pairing

variable {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

end Pairing

theorem exp_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f => ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

section Tangent

open GlobalTheory.ArcQ GlobalTheory.TorusTangent ReciprocityTheory.ChartRestriction.G.DVR

variable {K : Type} [Field K] {D₀ : Out.DegPre K}

variable [NumberField K]

end Tangent

section Exponents

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Type} [AddCommGroup X]
  [Module (𝓞 E) X] {g : ℕ} {ξ : Module.Dual ℤ X} {be : LinearMap.BilinForm ℤ X}

end Exponents

section Fibre

variable {K : Type} [Field K]

variable [NumberField K] {D₀ : Out.DegPre K}

end Fibre

variable {D : D7} {T : Core D} {j : ℕ}

section Family

variable {n' : ℕ} {La c₁ : ℝ}


end Family

section Comparison₂

variable {σ : T.Q.c.F →+* ℂ} {k : (T.U j σ).Comp} {x : ((T.U j σ).X k).dom} {ξ : Fin D.R.r → D.host.E}
  {ν : ((T.U j σ).X k).Ψ → ℝ} {lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E}


end Comparison₂

section Claims

variable {n' : ℕ} {La c₁ : ℝ} {Wp : ValuationSubring ℂ} {Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype}
  {σ : T.Q.c.F →+* ℂ} {k : (T.U j σ).Comp} {x : ((T.U j σ).X k).dom} {ξ : Fin D.R.r → D.host.E}
  {ν : ((T.U j σ).X k).Ψ → ℝ} {lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E}


end Claims

end GlobalTheory.CuspFamilyCompare
