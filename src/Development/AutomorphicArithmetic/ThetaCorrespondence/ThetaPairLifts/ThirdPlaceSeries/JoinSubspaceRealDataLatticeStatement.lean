module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.See
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.IndefiniteReal.RealPins
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelJoinOnV0Three
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinSubspaceRealDataLattice

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_subspace_real_data_exists_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), ∀ n : ℕ, SchurAll D → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) → Holds x.R x.F → x.A3.fam3.Ok3 n → x.A3.fam3.TypesSep3 → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).XE (divisionPairOfAdelicFormsFaceColumnsData x).I.eRR → RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc (S.toRealSpectralMatching Rc) (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @_root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt | exact _root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt | (intros; apply _root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt <;> assumption)
end
