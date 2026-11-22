module

public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapTheorem
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.RowChiReal
public import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
public import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended
public import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.LocDualOrth
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.QuotLen
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
public import Formalism.WachLatticeTwists.Statement
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
public import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
public import Formalism.CharacterColumnKernels.Statement
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Imports
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete
public import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement
public import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
public import Formalism.WachLatticeTwists.HodgeTateChains.Statement
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.FirstSummandActionMem
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bridge
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
public import Formalism.WachLatticeTwists.TorsionLengthCounts.RowCol
public import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG

theorem blk_ko {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type} {d : Type}
    [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {α : Type}
    [DecidableEq α] (bl : d → α)
    (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O) (k : α)
    (h : Fintype.card {a // bl a = k} = 1) : Nonempty (blockRestrictedRepresentationType bl ρk k ≃ₗ[O] KO O) := by
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 h
  exact ⟨(LinearEquiv.funUnique {a // bl a = k} O (KO O) : ({a // bl a = k} → KO O) ≃ₗ[O] KO O)⟩


end Formalism.RepresentationBoundsCohomology.FIN
