module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLatMul

theorem col_eq {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (a : B.A) (g h : GLw m w)
    (hh : h.val = GlobalTheory.TwLat.mulMat e b a * g.val) (j : Fin m) :
    ∑ i, e.symm (h.val i j) • b i = a * ∑ i, e.symm (g.val i j) • b i := by
  set M := LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) with hM
  have hij : ∀ i, e.symm (h.val i j) = ∑ k, M i k * e.symm (g.val k j) := by
    intro i
    rw [hh]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, GlobalTheory.TwLat.mulMat, map_sum, map_mul, hM]
  have hab : ∀ k, a * b k = ∑ i, M i k • b i := by
    intro k
    simp only [hM, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
    exact (b.sum_repr _).symm
  simp_rw [hij, Finset.mul_sum, mul_smul_comm, hab, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp_rw [mul_comm]

theorem lat_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (a : B.A) (g h : GLw m w), h.val = GlobalTheory.TwLat.mulMat e b a * g.val → GlobalTheory.TwLat.lat e b h = GlobalTheory.UnitLemma.mulLat K.O a (GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e _ _ _ B m b a g h hh
  unfold GlobalTheory.TwLat.lat GlobalTheory.UnitLemma.mulLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg _ (congrArg Set.range (funext fun j => ?_))
  exact col_eq e b a g h hh j

end GlobalTheory.TwLatMul
