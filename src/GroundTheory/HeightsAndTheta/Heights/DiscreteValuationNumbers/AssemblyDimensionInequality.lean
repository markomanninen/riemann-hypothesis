module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialPrimeOverZeroHeight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PQuotientHeightAddOne
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialDimensionInequality
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequalityOneGenerator
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequality
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PReesAlgebraDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem PolynomialDimensionInequality.full : PolynomialDimensionInequality.Statement.{u} :=
  PolynomialDimensionInequality.proof PolynomialPrimeOverZeroHeight.proof.{u}

theorem DimensionInequalityOneGenerator.full : DimensionInequalityOneGenerator.Statement.{u, v} :=
  DimensionInequalityOneGenerator.proof PolynomialDimensionInequality.full.{u}
    QuotientHeightAddOne.proof.{u}

theorem DimensionInequality.full : DimensionInequality.Statement.{u, v} :=
  DimensionInequality.proof DimensionInequalityOneGenerator.full.{u, v}
    DimensionInequalityOneGenerator.full.{v, v}

theorem ReesAlgebraDim.full : ReesAlgebraDim.Statement.{u} :=
  ReesAlgebraDim.proof DimensionInequality.full.{u, u}

theorem BlowUpModel.full : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof ReesAlgebraDim.full.{u}

end GroundTheory.Heights₂.Heights.NumbersDVR
