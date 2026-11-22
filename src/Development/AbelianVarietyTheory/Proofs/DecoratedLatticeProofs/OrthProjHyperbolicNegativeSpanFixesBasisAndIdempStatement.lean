module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanFixesBasisAndIdemp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthProjHyperbolicNegativeSpan_fixes_basis_and_idempotent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u ∧ ∀ y, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.prj X u y) = GlobalTheory.ScalW.prj X u y := by
  first | exact @GlobalTheory.ScalW.prj_fix_idem | exact GlobalTheory.ScalW.prj_fix_idem | (intros; apply GlobalTheory.ScalW.prj_fix_idem <;> assumption)
