module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReplacementValuesBaseLevelTypePartsEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
public import Lean
meta import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Mv

-- Use the kernel to compare fully elaborated types across the two stages.
open Lean Elab Tactic in
local elab "exact_by_kernel " term:term : tactic =>
  closeMainGoalUsing `exact_by_kernel fun target _ => do
    let value ← elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    let actual ← instantiateMVars (← Meta.inferType value)
    let target ← instantiateMVars target
    let lctx ← instantiateLCtxMVars (← getLCtx)
    match Kernel.isDefEq (← getEnv) lctx actual target with
    | .ok true => pure value
    | .ok false => throwError "expected{indentExpr target}\nbut the term has type{indentExpr actual}"
    | .error error => throwError (error.toMessageData (← getOptions))

local macro "kc%" t:term:max : term => `(by first | exact_by_kernel $t | with_unfolding_all exact ($t :))


section
variable {B : Base} {C : Cols B} {a : Late B C} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m}
  {R : RealDat3 a.D A Ks} {F : Face3 a.D A} {X0 : BaseLevelRowSide a.D} {Y : Read (A3 := A) R.toRealDat F.lv2 X0} (Z : ReadL R F X0 Y)
  (u : Parts R)

theorem jWu_heq : HEq (jWu Z u) Z.jW := by exact_by_kernel (HEq.refl Z.jW)

theorem eRRu_heq : HEq (eRRu Z u) Z.eRR := by exact_by_kernel (HEq.refl Z.eRR)

theorem eRR0u_heq : HEq (riemannRochSpaceCoordinateEquiv Z u) Z.eRR0 := by exact_by_kernel (HEq.refl Z.eRR0)

variable (c : Refill a)

theorem readL_jW : HEq (letI := alg c.to iK; (readL c Z).jW) Z.jW := by
  exact_by_kernel (jWu_heq Z (partsB c R))

theorem readL_eRR : HEq (letI := alg c.to iK; (readL c Z).eRR) Z.eRR := by
  exact_by_kernel (eRRu_heq Z (partsB c R))

theorem transportedReading_baseRowLatticeCoordinates : HEq (letI := alg c.to iK; (readL c Z).eRR0) Z.eRR0 := by
  exact_by_kernel (eRR0u_heq Z (partsB c R))

end


set_option maxHeartbeats 4000000 in
theorem rowsAre_refill : ∀ (B : Base) (C : Cols B) (a : Late B C) (c : Refill a) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (T : TwDat B) (Wt : Set B.places.Pl) (ix : C.Tup ≃ I.ι) (p0 : BaseLevelRowSide a.D) (r : RowsAre a.st I hX T Wt ix p0), ∃ r' : RowsAre c.to.st I hX T Wt ix (Tr.baseLevelRowSideTransport c p0), r'.z = Mv.cpDat c.to c.same r.z ∧ HEq r'.Y.tup r.Y.tup ∧ HEq r'.Y.tupT r.Y.tupT ∧ HEq r'.Y.PY.ψ r.Y.PY.ψ ∧ HEq (fun i => (r'.Y.PW i).ψ) (fun i => (r.Y.PW i).ψ) ∧ HEq (fun π => principalLevelFrame.rowRepR r'.z.R.θ (r'.Y.eFT π)) (fun π => principalLevelFrame.rowRepR r.z.R.θ (r.Y.eFT π)) ∧ HEq (fun x => (r'.Y.Ish.jE x).1) (fun x => (r.Y.Ish.jE x).1) ∧ HEq (fun x => (r'.Y.Iz.jE x).1) (fun x => (r.Y.Iz.jE x).1) ∧ HEq r'.Y.eE r.Y.eE ∧ HEq r'.Y.jA r.Y.jA ∧ HEq r'.Y.jA0 r.Y.jA0 ∧ HEq r'.Y.eMt r.Y.eMt ∧ HEq r'.Y.mj.eW r.Y.mj.eW ∧ HEq r'.Z.jW r.Z.jW ∧ HEq r'.Z.eRR r.Z.eRR ∧ HEq r'.Z.eRR0 r.Z.eRR0 := by
  intro B C a c px I hX T Wt ix p0 r
  letI := r.z.alg
  refine ⟨⟨Mv.cpDat c.to c.same r.z, (kc% (holds_tr c.to r.intersectionNumber_baseChange)), (kc% (read c r.Y)), (kc% (readL c r.Z)),
    (kc% r.tup_ix)⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_by_kernel (HEq.refl r.Y.tup)
  · exact (kc% (HEq.refl r.Y.tupT))
  · exact (kc% (HEq.refl r.Y.PY.ψ))
  · exact (kc% (HEq.refl (fun i => (r.Y.PW i).ψ)))
  · exact (kc% (heq_of_eq (funext fun π => (rep_eq c r.Y π).symm)))
  · exact_by_kernel (HEq.refl (fun x => (r.Y.Ish.jE x).1))
  · exact_by_kernel (HEq.refl (fun x => (r.Y.Iz.jE x).1))
  · exact (kc% (HEq.refl r.Y.eE))
  · exact (kc% (HEq.refl r.Y.jA))
  · exact (kc% (HEq.refl r.Y.jA0))
  · exact (kc% (HEq.refl r.Y.eMt))
  · exact (kc% (HEq.refl r.Y.mj.eW))
  · exact (kc% (readL_jW r.Z c))
  · exact (kc% (readL_eRR r.Z c))
  · exact (kc% (transportedReading_baseRowLatticeCoordinates r.Z c))

end GlobalTheory.Mem.R3.Rw.Mv

end
