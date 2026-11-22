module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataColumns
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasureIsomorphismAtInfinity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion

@[expose] public section

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.L2.SG.TypedSets

theorem inColumnsAt_holds :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InColumnsAt X hb hK FdN FdN' u u' X0 L A :=
  massDataColumns_of' Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Closed.AdBridgeGF_holds
    Formalism.L2.SG.Closed.AdBridgeK_holds
    (fun X u hK => Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK))
    (fun X u hK => Formalism.L2.SG.Closed.ClassFin_holds X u hK)
    (fun I hb => ⟨Formalism.L2.SG.Pf.Meas.eFin I hb, fun _ => rfl⟩)
    (fun X => Formalism.L2.SG.Pf.level_subgroup_compact_open X)
    Formalism.L2.SG.Closed.AutKCompact_holds
    Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

end Formalism.L2.SG.Pf.MassDataX
