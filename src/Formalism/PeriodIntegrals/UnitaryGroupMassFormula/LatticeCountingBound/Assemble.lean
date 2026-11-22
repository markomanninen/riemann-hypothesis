module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.LatCountAllOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SublatticeOfLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.LatticeIsDiscreteGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.NormProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.DetMono
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.PackLem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchIneq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.DualIncl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Choose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchPlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDual

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LCG

theorem latCountAll_of_steps (hB : BoxBound) (hP : PackLem) (hD : DualIncl) (hCh : Choose) (hA : ArchIneq)
    (hAP : ArchPlaceOf) (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of hB lattice_map_image sublattice_of_lattice
    (separation_of_points lattice_is_discrete_group hD hCh (hAP hA) hI PI.UnitaryGroupMassFormula.LSC.norm_product_formula PI.UnitaryGroupMassFormula.LSC.determinant_monotone card_places_bound)
    hP norm_positive card_places_bound

theorem latCountAll_of_open (hD : DualIncl) (hCh : Choose) (hAP : ArchPlaceOf) (hI : IndexIneq) :
    PI.LatCountG.LatCountAll :=
  latCountAll_of_steps box_lattice_point_bound lattice_packLem hD hCh archimedean_inequality hAP hI

theorem latCountAll_of_open2 (hAP : ArchPlaceOf) (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of_open dual_lattice_inclusion choice_of_generators hAP hI

theorem latCountAll_of_index (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of_open2 archimedean_place_exists hI

theorem latCountAll_of_idx (hD2 : DetIdx) (hIO : IndexOf) : PI.LatCountG.LatCountAll :=
  latCountAll_of_index (hIO dual_index_formula hD2)

end PI.UnitaryGroupMassFormula.LCG
