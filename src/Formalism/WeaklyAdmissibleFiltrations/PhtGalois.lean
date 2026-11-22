module

public import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Galois
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.TrivCrys
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExLattice
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExistsPeriodRingDataHolds
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.WachCol
public import Formalism.WeaklyAdmissibleFiltrations.StatementPC
public import Formalism.CoboundaryTransfers.StatementAPI
public import Formalism.CoboundaryTransfers.WachBridges
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.DPotCrisStableAndExistsPotentiallyCrystallineDat
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

namespace Formalism.WeaklyAdmissibleFiltrations

theorem pht_galois : CobF ∧ TorsFreeT ∧ CocyclesFunctorial ∧ ImFLe ∧ TrivCrys ∧ ExLattice ∧ ExPD ∧ WachCol :=
  ⟨finiteCocycles_properties.1, finiteCocycles_properties.2.1, finiteCocycles_properties.2.2.1, finiteCocycles_properties.2.2.2, trivialIsCrystalline_holds,
    existsStableLattice_holds, existsPeriodRingData_holds, cokernelLengthEqWach_holds⟩

end Formalism.WeaklyAdmissibleFiltrations
