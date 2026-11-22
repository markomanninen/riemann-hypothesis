module

public import Development.EtaleCohomology.CyclotomicDiscriminants.SSteinTPf

@[expose] public section

namespace LateralTheory.Fin.SStein
theorem stein_statement_holds : UpperTheory.V.ZK.SStein := by
  apply LateralTheory.Q.SSteinT.SStein_of
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SStein := stein_statement_holds
end LateralTheory.Fin.SStein
