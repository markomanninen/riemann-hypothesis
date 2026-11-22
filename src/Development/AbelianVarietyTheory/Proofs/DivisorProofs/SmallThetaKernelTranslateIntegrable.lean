module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevelStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallConv

theorem splitBound_ge : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ _ => 11 ≤ D.host.splitBound := by
  exact ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS _ _ _ => hS.size.2.1.eleven_le⟩⟩

theorem standing : Big fun ch => ∀ t, SquareStanding ch.G t := by
  obtain ⟨CF0, hH⟩ := splitBound_ge.and GlobalTheory.T.test_places_prime_to_level
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc t => ?_⟩
  obtain ⟨h11, hW⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · exact hW w hw
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

end GlobalTheory.SmallConv

end
