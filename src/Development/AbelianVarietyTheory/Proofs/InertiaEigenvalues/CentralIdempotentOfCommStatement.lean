module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfComm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

@[expose] public section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admALG_of_commG_var : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := by
  first | exact @GlobalTheory.IdemAlg.admALG_of_commG | exact GlobalTheory.IdemAlg.admALG_of_commG | (intros; apply GlobalTheory.IdemAlg.admALG_of_commG <;> assumption)
