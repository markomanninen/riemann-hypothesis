module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsProj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhSchurConv
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhConvProj
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhProdConv
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdIndexEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionD
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfLowest
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhLocOfIntegrablePh

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.RowsCount


open Formalism Formalism.L2 Formalism.L2.SG in
theorem projRowsR : Formalism.L2.SG.ProjRows.ProjRowsR :=
  Formalism.L2.SG.ProjRows.projRowsR_of schur_orthogonality_idempotent convolution_projection isConvIdempotent_pi
    Formalism.L2.SG.Pf.regular_representation_unitary


open Formalism Formalism.L2 Formalism.L2.SG in
theorem unimodGf : Formalism.L2.SG.Pf.UnimodGf := fun I μf _ _ =>
  (PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable
    PI.adelic_index_eq) I μf inferInstance

theorem D_eq_finrank_HHX : ∀ (D : D7) (X : HidaSetting D),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → X.B.D = Module.finrank ℂ (HHX X) := by
  intro D X h
  exact (Formalism.L2.SG.RowsDef.RowsAut.D_eq_finrank_HH (Formalism.L2.SG.Pf.rows_bijective projRowsR unimodGf) X.B _
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X) (fun v => (X.low v).1)
    (GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X h) X.Rph X.Rph_spec).1

end GlobalTheory.RowsCount
