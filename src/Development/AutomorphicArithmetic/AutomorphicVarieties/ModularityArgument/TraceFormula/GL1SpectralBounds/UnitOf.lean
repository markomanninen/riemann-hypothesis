module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.SecondFromFirstStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

@[expose] public section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

theorem UpperTheory.V.Z.Tf.GOne.unitOf :
    UnitOf := by
  intro E _ _ _ n _ π h
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired UpperTheory.V.Af.formsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) h
  exact (CG.isUnitary_mk π).2
    (GlobalTheory.SpehPair.isUnitary_of_isNormalised (GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc))
