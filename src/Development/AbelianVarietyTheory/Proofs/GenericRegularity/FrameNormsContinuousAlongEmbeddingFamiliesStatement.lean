module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
public import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
public import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
public import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameNorms_continuous_along_embedding_families : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ [Fintype (Comp Xo c)], ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → NrmAlong fn yP ∧ ∀ (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)), STLoc h Dd N uL wR jc → FnTrdeg Xo c Dd → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → NrmContOff h fn yP Dd N uL wR jc := by
  first | exact @GlobalTheory.FrameNorm.nrmAlong_of_fnPin | exact GlobalTheory.FrameNorm.nrmAlong_of_fnPin | (intros; apply GlobalTheory.FrameNorm.nrmAlong_of_fnPin <;> assumption)
