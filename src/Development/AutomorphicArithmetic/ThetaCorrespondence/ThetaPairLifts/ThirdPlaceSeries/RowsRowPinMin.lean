module

public import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPin

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure RowPinMinAlt (T : _root_.Formalism.L2.TiedDataSKAlt ex) : Prop where
  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)
  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1
  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂
end Formalism.L2.Rows
end
end
