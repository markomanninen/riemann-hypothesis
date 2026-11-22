module

public import Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapSecondPlace
public import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
public import Mathlib
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.CoboundaryTransfers.StatementAPI
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
public import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
public import Formalism.WachLatticeTwists.Statement
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
public import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
public import Formalism.CharacterColumnKernels.Statement
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Imports
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete
public import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement
public import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
public import Formalism.WachLatticeTwists.HodgeTateChains.Statement
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
public import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
public import Formalism.WachLatticeTwists.RealDisplaySplitting.SurjectionRankOneIdempotent
public import Formalism.WachLatticeTwists.RamifiedBlockRings.LocalToDisplayFree
public import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended
public import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.LocDualOrth
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.QuotLen
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.FirstSummandActionMem
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bridge
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
public import Formalism.WachLatticeTwists.TorsionLengthCounts.RowCol
public import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveReal
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.InRowRealOf
public import Formalism.LagrangeIdealLifts.Statement
public import Formalism.CoboundaryTransfers.GammaStableTransfers.MemCoboundariesOfIsOneCoboundary
public import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds
public import Formalism.CoboundaryTransfers.GammaStableTransfers.DiffOneSmulOfTower
public import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.IdempotentRankOneAtPoint
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveRealAllLiftThird

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem nonempty_pl : Nonempty (HeightOneSpectrum (𝓞 D.host.E)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
    (NumberField.RingOfIntegers.not_isField _)⟩⟩

def plSet : Finset (HeightOneSpectrum (𝓞 D.host.E)) := dc.row ∪ dc.col ∪ D.nd.Q i

def idx (v : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  if h : v ∈ plSet i dc then ((plSet i dc).equivFin ⟨v, h⟩ : ℕ) else (plSet i dc).card

def plOf (n : ℕ) : HeightOneSpectrum (𝓞 D.host.E) :=
  if h : n < (plSet i dc).card then ((plSet i dc).equivFin.symm ⟨n, h⟩ : HeightOneSpectrum (𝓞 D.host.E))
  else Classical.choice nonempty_pl

theorem plOf_idx {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ plSet i dc) : plOf i dc (idx i dc v) = v := by
  unfold plOf idx
  rw [dite_eq_left h, dite_eq_left ((plSet i dc).equivFin ⟨v, h⟩).isLt]
  simp

theorem idx_inj {v w : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ plSet i dc) (hw : w ∈ plSet i dc)
    (h : idx i dc v = idx i dc w) : v = w := by
  calc v = plOf i dc (idx i dc v) := (plOf_idx i dc hv).symm
    _ = plOf i dc (idx i dc w) := by rw [h]
    _ = w := plOf_idx i dc hw

def rowsN : Finset ℕ := dc.row.image (idx i dc)
def colsN : Finset ℕ := dc.col.image (idx i dc)
def qsN : Finset ℕ := (D.nd.Q i).image (idx i dc)

abbrev Col : Type := {u : HeightOneSpectrum (𝓞 D.host.E) // u ∈ dc.col}

def colIdx (l : Col i dc) : ℕ := idx i dc l.1

theorem colIdx_inj : Function.Injective (colIdx i dc) := by
  intro l₁ l₂ h
  apply Subtype.ext
  have m₁ : l₁.1 ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ l₁.2)
  have m₂ : l₂.1 ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ l₂.2)
  exact idx_inj i dc m₁ m₂ h

def Aw (n : ℕ) : ValuationSubring D.nd.Om := D.nd.plOm.1 (plOf i dc n)
def Av (v : HeightOneSpectrum (𝓞 D.host.E)) : ValuationSubring D.nd.Om := D.nd.plOm.1 v

end Formalism.MainNotions.N.K

end
