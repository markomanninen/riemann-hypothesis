module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataTies
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdFrame

theorem vStd_of_orthonormal_span : ∀ (D : D7) (i : Fin D.R.m), ((∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → VStd D i := by
  intro D i h
  refine vStd_of_frameChoice D i ⟨h.1, fun a => ?_⟩
  show (Vc D i).frame a ∈ (Vc D i).L0
  rw [h.2]
  exact Submodule.subset_span ⟨a, rfl⟩

end GlobalTheory.StdFrame
