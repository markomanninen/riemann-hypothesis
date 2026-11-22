module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain

@[expose] public section

noncomputable section

namespace GlobalTheory.Pdv

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host NumberField IsDedekindDomain

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def At (ex : Extra D L hT Gi Gl K Y cX) (E : KerEnt D Y ex.tw) : Prop :=
  (E.UnUnit ∧ OrbitPlaces.KmapRat E ∧ OrbitPlaces.KFi D ex.tw ∧ OrbitPlaces.Stab0 D) ∧
    ∃ (ep : _) (be : _) (sg : _),
      OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Gi K ∧ OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.Shape D L Gi (OrbitPlaces.ofKer (nuRowOK D) E ep be sg)

variable {ex : Extra D L hT Gi Gl K Y cX}

def IsEntC (t : KerEntTied ex) : Prop :=
  ∃ (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (h : KerEntHyp P t.O B Y ex.tw), t.ent = kerEntC P t.O B h

structure Duty (t : KerEntTied ex) : Prop where
  col : GlobalTheory.KerJ.ColSide t
  entC : IsEntC t
  rk : t.RK
  forms : ∃ t' : KerEntTied ex, GlobalTheory.KerJ.ColSide t' ∧ GlobalTheory.KerJ.FormsPin t'

end GlobalTheory.Pdv

end
