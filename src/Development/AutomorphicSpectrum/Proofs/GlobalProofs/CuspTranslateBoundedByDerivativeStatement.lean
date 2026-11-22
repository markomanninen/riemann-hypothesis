module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CuspTranslateBoundedByDerivative

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.cusp_translate_bounded_by_derivative : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.SmoothForms.LieN V) (φ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ‖GlobalTheory.Cusp.Rcusp V μ (GlobalTheory.SmoothForms.expInf θ V X) (GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ) - GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ‖ ≤ ‖GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.derInf hθ X φ)‖ :=
  @GlobalTheory.CompanionTheory.HCCusp.norm_Rcusp_expInf_sub_le
