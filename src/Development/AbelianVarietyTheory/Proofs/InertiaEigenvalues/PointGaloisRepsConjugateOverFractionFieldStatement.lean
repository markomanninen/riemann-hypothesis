module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointGaloisRepsConjugateOverFractionField
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointGaloisReps_conjugate_over_fraction_field : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  first | exact @GlobalTheory.PointRepConj.main | exact GlobalTheory.PointRepConj.main | (intros; apply GlobalTheory.PointRepConj.main <;> assumption)
