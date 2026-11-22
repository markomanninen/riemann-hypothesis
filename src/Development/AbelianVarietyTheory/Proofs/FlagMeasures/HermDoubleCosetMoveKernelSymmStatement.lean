module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMoveKernelSymm
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermDoubleCosetMoveKernel_symm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → S.kern β (j + 1) βJ d Λ Λ' = S.kern β (j + 1) βJ d Λ' Λ := by
  first | exact @GlobalTheory.HL.KernSym.kern_symm | exact GlobalTheory.HL.KernSym.kern_symm | (intros; apply GlobalTheory.HL.KernSym.kern_symm <;> assumption)
