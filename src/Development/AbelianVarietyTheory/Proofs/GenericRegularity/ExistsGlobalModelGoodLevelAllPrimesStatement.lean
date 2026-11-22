module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimes
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
theorem _root_.GlobalTheory.T.exists_global_model_goodLevel_all_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → (∀ la, ModelAt Xo c la) ∧ Nonempty (Model Xo c (algebraMap (𝓞 c.F) c.F)) := by
  first | exact @GlobalTheory.Reg.modelAt_and_nonempty_global_model | exact GlobalTheory.Reg.modelAt_and_nonempty_global_model | (intros; apply GlobalTheory.Reg.modelAt_and_nonempty_global_model <;> assumption)
