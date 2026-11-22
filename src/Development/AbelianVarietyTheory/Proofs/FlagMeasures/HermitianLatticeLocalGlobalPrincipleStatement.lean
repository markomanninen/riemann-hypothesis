module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_local_global_principle : ∀ (D : D7) (Z : LocDat D), (∀ Λ₁ Λ₂ : LV D, Submodule.IsFullLattice D.host.E Λ₁ → Submodule.IsFullLattice D.host.E Λ₂ → {p | lattice₂ D Z.M p Λ₁ ≠ lattice₂ D Z.M p Λ₂}.Finite ∧ ((∀ p, lattice₂ D Z.M p Λ₁ = lattice₂ D Z.M p Λ₂) → Λ₁ = Λ₂)) ∧ ∀ (Λ₀ : LV D), Submodule.IsFullLattice D.host.E Λ₀ → ∀ Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p), (∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤) → {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite → ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ = Lp p := by
  first | exact @GlobalTheory.Unfold.LatLoc.lattices_local_global | exact GlobalTheory.Unfold.LatLoc.lattices_local_global | (intros; apply GlobalTheory.Unfold.LatLoc.lattices_local_global <;> assumption)
