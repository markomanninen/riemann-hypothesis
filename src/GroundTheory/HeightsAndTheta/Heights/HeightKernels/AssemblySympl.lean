module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplTop
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOmegaMem
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplCons
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplExtMem
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplExtVecMul
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplTwoRow
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplGcd
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOrbit
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplQuadDiag
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplBoxVolume
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinkowskiBox
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinExists
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplShortPrim
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplGramMem
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplFirstRow
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceMem
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReducePosDef
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceConj
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetSchur
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceStep
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplStep
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetBound

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SymplOmegaMem.full : SymplOmegaMem.Statement :=
  SymplOmegaMem.proof

theorem SymplCons.full : SymplCons.Statement :=
  SymplCons.proof

theorem SymplExtVecMul.full : SymplExtVecMul.Statement :=
  SymplExtVecMul.proof

theorem SymplTwoRow.full : SymplTwoRow.Statement :=
  SymplTwoRow.proof

theorem SymplGcd.full : SymplGcd.Statement :=
  SymplGcd.proof

theorem SymplQuadDiag.full : SymplQuadDiag.Statement :=
  SymplQuadDiag.proof

theorem SymplBoxVolume.full : SymplBoxVolume.Statement :=
  SymplBoxVolume.proof

theorem SymplShortPrim.full : SymplShortPrim.Statement :=
  SymplShortPrim.proof

theorem SymplGramMem.full : SymplGramMem.Statement :=
  SymplGramMem.proof

theorem SymplReducePosDef.full : SymplReducePosDef.Statement :=
  SymplReducePosDef.proof

theorem SymplReduceConj.full : SymplReduceConj.Statement :=
  SymplReduceConj.proof

theorem SymplDetSchur.full : SymplDetSchur.Statement :=
  SymplDetSchur.proof

theorem SymplExtMem.full : SymplExtMem.Statement :=
  SymplExtMem.proof SymplOmegaMem.full SymplCons.full

theorem SymplMinkowskiBox.full : SymplMinkowskiBox.Statement :=
  SymplMinkowskiBox.proof SymplBoxVolume.full

theorem SymplMinExists.full : SymplMinExists.Statement :=
  SymplMinExists.proof SymplQuadDiag.full

theorem SymplReduceMem.full : SymplReduceMem.Statement :=
  SymplReduceMem.proof SymplOmegaMem.full SymplCons.full

theorem SymplOrbit.full : SymplOrbit.Statement :=
  SymplOrbit.proof SymplExtMem.full SymplExtVecMul.full SymplTwoRow.full SymplGcd.full SymplCons.full

theorem SymplMinBound.full : SymplMinBound.Statement :=
  SymplMinBound.proof SymplQuadDiag.full SymplMinkowskiBox.full

theorem SymplReduceStep.full : SymplReduceStep.Statement :=
  SymplReduceStep.proof SymplExtMem.full SymplReduceConj.full SymplDetSchur.full

theorem SymplFirstRow.full : SymplFirstRow.Statement :=
  SymplFirstRow.proof SymplMinExists.full SymplMinBound.full SymplOrbit.full SymplShortPrim.full SymplGramMem.full

theorem SymplStep.full : SymplStep.Statement :=
  SymplStep.proof SymplFirstRow.full SymplGramMem.full SymplReduceMem.full SymplReducePosDef.full SymplReduceStep.full

theorem SymplDetBound.full : SymplDetBound.Statement :=
  SymplDetBound.proof SymplStep.full

theorem SymplecticReduction.full : SymplecticReduction.Statement :=
  SymplecticReduction.proof SymplStep.full SymplDetBound.full

end GroundTheory.Heights₂.Heights
