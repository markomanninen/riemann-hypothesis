module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalH
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfGTerm
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DCount
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DRepsP

@[expose] public section

namespace UpperTheory.Esk

theorem holWC : HolWC := holWC_of dAx dTwo' dGood' dReps (pf_GTerm s_GCh s_GUnit s_GMod)

end UpperTheory.Esk
