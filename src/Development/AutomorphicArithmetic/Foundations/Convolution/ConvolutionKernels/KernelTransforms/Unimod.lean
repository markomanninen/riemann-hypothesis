module

public import Mathlib
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
public import GroundTheory.AutomorphicForms.TraceFormulaConvolution
public import GroundTheory.AutomorphicForms.TraceFormulaWeil
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
public import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
public import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchHaar

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.unimod :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure], ν.IsMulRightInvariant ∧ ν.IsInvInvariant) ∧
      ∀ (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], m.IsMulRightInvariant ∧ m.IsInvInvariant := by
  intro K _ _ n
  refine ⟨fun ν _ => ⟨isMulRightInvariant_archGroup ν, isInvInvariant_archGroup ν⟩, fun m _ => ?_⟩
  haveI hr : m.IsMulRightInvariant := Whittaker.isMulRightInvariant_finite K n m
  exact ⟨hr, ⟨inv_eq_self_of_isMulRightInvariant m⟩⟩
