module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLocusDecomposesOverCoefRingOfChebotarev
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLocusDecomposesOverCoefRing_of_chebotarev : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D → ∀ i : D.nd.Loc, ZDecomp D.nd i := by
  first | exact @GlobalTheory.ZDecompAt.zDecomp_of_cheb | exact GlobalTheory.ZDecompAt.zDecomp_of_cheb | (intros; apply GlobalTheory.ZDecompAt.zDecomp_of_cheb <;> assumption)
