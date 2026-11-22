module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorGramMatrixConstDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset : ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T'), Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  first | exact @GlobalTheory.leadMinorE_zhatL_dcrel | exact GlobalTheory.leadMinorE_zhatL_dcrel | (intros; apply GlobalTheory.leadMinorE_zhatL_dcrel <;> assumption)
