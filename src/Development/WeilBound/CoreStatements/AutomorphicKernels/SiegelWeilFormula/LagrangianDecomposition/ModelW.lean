module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ExistsSchwartzOneCpt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SchrTransl
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem modelEx_wired (hD : SDarb) (hP : PartCharInv) (hC : ChartFacts) (hG : SiegelSmall) (hS : SmallS) : ModelEx :=
  modelEx_of hD PositivityTheory.SiegelWeilFormula.Ldexa.sEv bigT sliceFacts (opBox_of hP sliceFacts) (subSplit_of sliceFacts) hC hG hS

end PositivityTheory.SiegelWeilFormula.Ald

end
