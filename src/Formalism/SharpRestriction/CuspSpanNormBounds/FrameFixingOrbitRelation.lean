module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.S.TieN

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mass

open Formalism.MainNotions.S.LocalSplitGroups

end Mass

section Cnt

open IsDedekindDomain MeasureTheory Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical

variable {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

def IntLow {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ} (l : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a, l a a = 1) ∧ (∀ a b, a < b → l a b = 0) ∧ ∀ a b, l a b ∈ Mp.R

def IntUp {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ} (ρ : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ Mp.R

end Cnt

section Cnt2

open IsDedekindDomain MeasureTheory Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical

variable {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

end Cnt2

section FromLoc

open Formalism.MainNotions.S.LocalSplitGroups

end FromLoc

section Orb

open MeasureTheory Matrix Formalism.QuantumDeterminants

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {Cw : ℝ}

end Orb

end Formalism.MainNotions.S.TieN
