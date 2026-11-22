module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisConvOfSteps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SwSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralNeTopOfBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TermInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerAbsOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspKillHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OmRatInvApply

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory.RawLift.Assembled

theorem rallisConv_of_siegelWeil : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    ∀ D : D7, GlobalTheory.RawLift.RallisConv D :=
  fun hP hW D => GlobalTheory.RawLift.rallisConv_of_steps D (GlobalTheory.SWPairProof.swPair hW D) (GlobalTheory.EisAbsPf.eisAbs hP D)
    (GlobalTheory.RawLift.kerAbs_of_cuspRapidDecay hP D) (GlobalTheory.RawLift.Move.termMove D) (GlobalTheory.TermInvProof.termInv D)
    (GlobalTheory.CuspKillProof.cuspKill_holds D)

end GlobalTheory.RawLift.Assembled
