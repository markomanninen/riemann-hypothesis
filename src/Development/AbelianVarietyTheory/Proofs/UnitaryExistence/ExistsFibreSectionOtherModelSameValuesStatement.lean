module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionOtherModelSameValues
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
theorem _root_.GlobalTheory.T.exists_fibreSection_other_model_same_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec), ∃ s' : LB.Sec (PPx y), ∀ j (pt : Sp ℂ ⟶ Gx y) (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y), x ≫ pullback.fst _ _ = pt ≫ gxFst y → x ≫ pullback.snd _ _ = 𝟙 _ → pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U (fun _ => j)) (s'.f (fun _ => j)) = valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) := by
  first | exact @GlobalTheory.FibreSection.exists_sec_same_values | exact GlobalTheory.FibreSection.exists_sec_same_values | (intros; apply GlobalTheory.FibreSection.exists_sec_same_values <;> assumption)
