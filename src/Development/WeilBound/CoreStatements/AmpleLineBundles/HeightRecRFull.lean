module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightAssemblyFull
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatio
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitLocalSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterZero
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartRing
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartQuot
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartDehom
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCard
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredPlacesFinite
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredRingNormal
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalNormalIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCentred
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlacesRingQuot
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalLengthPlaces
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterChart
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartTerm
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterLe
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterPrime
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSupp
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveIsOrbit
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.PNefOnFibresRelabel

@[expose] public section

namespace CoverDenseAlt
open GroundTheory.Heights₂.Heights

theorem heightRecR_full : HeightRecR.Statement :=
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  HeightRecR.proof OrbitDivVertical.proof
    (OrbitFiniteSum.proof OrbitDegreeRatio.proof
      (OrbitLocalSum.proof OrbitChartRing.proof hM
        (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
        OrbitChartMult.proof
        (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
          (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
        OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof)
      (OrbitCenterZero.proof OrbitCenterLe.proof hIff
        (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)))
    (OrbitArchSum.of_conjSum OrbitConjSum.proof)

theorem chartDehom_full : OrbitChartDehom.Statement :=
  OrbitChartDehom.proof OrbitChartMax.proof OrbitChartQuot.proof

end CoverDenseAlt
