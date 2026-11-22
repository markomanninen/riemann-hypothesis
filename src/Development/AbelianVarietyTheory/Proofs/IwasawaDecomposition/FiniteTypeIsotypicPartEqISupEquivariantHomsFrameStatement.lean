module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypeIsotypicPartEqISupEquivariantHomsFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteTypeIsotypicPart_eq_iSup_equivariantHoms_frame : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f := by
  first | exact @GlobalTheory.IsotHom.isotIn_eq_iSup_homInto | exact GlobalTheory.IsotHom.isotIn_eq_iSup_homInto | (intros; apply GlobalTheory.IsotHom.isotIn_eq_iSup_homInto <;> assumption)
