module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional

@[expose] public section

namespace GlobalTheory

theorem rowsFinDim_link : Formalism.L2.SG.RowsDef.RowsFinDim :=
  CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional

end GlobalTheory
