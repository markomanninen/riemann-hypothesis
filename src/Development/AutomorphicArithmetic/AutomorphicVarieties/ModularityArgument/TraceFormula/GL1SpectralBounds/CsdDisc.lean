module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

@[expose] public section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

theorem UpperTheory.V.Z.Tf.GOne.csdDisc :
    CsdDisc := by
  intro E _ _ _ n _ π h
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) h
  have hn : IsNormalised π := GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc
  refine isDiscrete_of_cuspSub π fun φ hφ => ?_
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_invariant (π.cusp φ hφ) (hn φ hφ)
  exact GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) (C := C) fun g => by simpa using hC g
