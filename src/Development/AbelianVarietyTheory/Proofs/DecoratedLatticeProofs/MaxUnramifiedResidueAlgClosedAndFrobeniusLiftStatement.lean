module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaxUnramifiedResidueAlgClosedAndFrobeniusLift
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxUnramified_residueAlgClosed_and_frobeniusLift : ∀ (l : ℕ) [Fact l.Prime], 2 < l → ResAlg (MaximalUnramifiedExtension l) ∧ ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension l) l σ → Unr (MaximalUnramifiedExtension l) l σ := by
  first | exact @GlobalTheory.Honda.kur_resAlg_unr | exact GlobalTheory.Honda.kur_resAlg_unr | (intros; apply GlobalTheory.Honda.kur_resAlg_unr <;> assumption)
