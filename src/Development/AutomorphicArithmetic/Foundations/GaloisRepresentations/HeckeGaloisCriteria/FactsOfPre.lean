module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Tie0CutOfTie0
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.CompatibilityTiesEigenRestriction
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExistsUnitOneAddGenerator
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProductStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpolyStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZeroStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingletonStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRank
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointConditionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory Tr

variable {D : D7}


set_option maxHeartbeats 1000000 in
@[reducible] def nchCut (c : CutD D) (x : NChoice D) : NChoice (cut D c) := { x with }

set_option maxHeartbeats 1000000 in
theorem nct_cut (c : CutD D) {x : NChoice D} (h : NChTie D x) : NChTie (cut D c) (nchCut c x) :=
  { h with
    twOf_eq := fun a => h.twOf_eq a.1
    twSide_eq := fun a => h.twSide_eq a.1
    Q_eq := fun a => h.Q_eq a.1
    psi_eq := h.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

end UpperTheory.GalC
