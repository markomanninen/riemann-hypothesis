module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_along_tangent_combination_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), (∀ i, IsTanAt x (v i)) → IsCombAt x v a w → ∀ (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)), TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom ((w.appLE U ⊤ h).hom f)) = ∑ i, a i * TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom (((v i).appLE U ⊤ (hv i)).hom f)) := by
  first | exact @GlobalTheory.TanDeriv.deriv_comb | exact GlobalTheory.TanDeriv.deriv_comb | (intros; apply GlobalTheory.TanDeriv.deriv_comb <;> assumption)
