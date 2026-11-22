module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfPrimesRel
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitOfPoints
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightWindowRequirementHostOfPoint
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProofStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatumStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasWithDutyWallAndChoices
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FixAndWinOfNumAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersAdmissible
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RecExGOfRecAtG
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwGoodOneSetDiv

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem isSel_of_sAnd {Bd : BdT} {Q R : V4.Slot} {Lk : LkT Bd} {E : Par → BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜}
    (s : IsSel (sAnd Q R) Lk E 𝒜 σ) : IsSel Q Lk E 𝒜 σ := by
  intro eps Fm hc
  obtain ⟨κ, h1, h2, h3⟩ := s Fm hc
  refine ⟨κ, h1, h2, fun x hx i => ⟨?_, (h3 x hx i).2⟩⟩
  obtain ⟨K, β, b, a0, a1, a2, a3⟩ := (h3 x hx i).1
  exact ⟨K, β, b, a0, a1.1, a2, a3⟩

end GlobalTheory.Fc
