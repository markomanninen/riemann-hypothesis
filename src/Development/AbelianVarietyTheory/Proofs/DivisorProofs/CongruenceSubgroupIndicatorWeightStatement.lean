module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceSubgroupIndicatorWeight
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_indicator_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n → 1 ≤ k → Match n a b w 1 ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) (fun y : GLw a w × GLw b w => ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  first | exact @GlobalTheory.CongMatch.match_principal_congruence_inert | exact GlobalTheory.CongMatch.match_principal_congruence_inert | (intros; apply GlobalTheory.CongMatch.match_principal_congruence_inert <;> assumption)
