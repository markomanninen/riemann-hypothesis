module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.CarriedPlMap
public import Formalism.LocalToGlobal.SelSide
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.ColPins
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentificationsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPointsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheoremsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingDefiniteBaseVanishOfMiStar2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeOpEqSpanOfFormsTie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
public import Formalism.LocalToGlobal.IndefiniteReal.CutPassage
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalRingCardinality.DataBu
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.DivLinked

section Read

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}


set_option maxHeartbeats 2000000 in
theorem divisionRows_pairing_vanishes_of_rational_pairing_law
    (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧
      GlobalTheory.Published.CuspRapidDecay) (x : GlobalTheory.Mem.R3.TwIn ex) (hH : Holds x.R x.F) (hB : Rw.BkLaw D)
    (hV : CxData.BtVanish (fc := x.F.fc) (x.R.toCx3 x.F)) : GlobalTheory.Cp.DivRows3G (GlobalTheory.Mem.R3.divisionPairOfAdelicFormsFaceColumnsData x) := by
  have hRational := GlobalTheory.T.divisionPairing_rational_on_rationalPoints'
    hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.pins hH
  have hRows := (GlobalTheory.T.divisionCompatible_at_readIdentifications
    hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.sEE Yd x.JM x.pins hH
    (fun _ _ => x.div.grp)).2 x.mjH ex.idx (hB hRational) hV
  exact {
    sharpRR := hRows.sharpRR
    baseRR := hRows.baseRR
    divisionRows_rationalLift := fun i t _ => hRows.divisionRows_rationalLift i t
    thTheta := fun i t _ v => hRows.thTheta i t v
    num := ⟨fun i t _ w => hRows.num.Ij i t w, fun i t _ w => hRows.num.jw i t w, hRows.num.etaJ⟩
    colsBk := hRows.colsBk }

end Read

end GlobalTheory.Fc.DivLinked

end
