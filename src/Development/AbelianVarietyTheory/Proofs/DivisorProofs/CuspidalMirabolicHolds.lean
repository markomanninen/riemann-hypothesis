module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.CuspidalMirabolic

@[expose] public section

namespace GlobalTheory

theorem cuspidalMirabolic_holds : GlobalTheory.Published.CuspidalMirabolic :=
  CompanionTheory.Mirab.cuspidalMirabolic

end GlobalTheory
