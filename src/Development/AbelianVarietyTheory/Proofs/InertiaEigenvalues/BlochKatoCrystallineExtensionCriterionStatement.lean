module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_crystalline_extension_criterion : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  first | exact @GlobalTheory.ExtCrysCrit.blochKato_ext_all | exact GlobalTheory.ExtCrysCrit.blochKato_ext_all | (intros; apply GlobalTheory.ExtCrysCrit.blochKato_ext_all <;> assumption)
