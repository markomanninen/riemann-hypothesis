module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.RealPins
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Formalism.LocalRingCardinality.DataNChTie
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFirst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassSumPinT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NXNMjT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionFirstStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionSecondAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EMEqThPeStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.BigTop.PtAt.nmjT_at_tied_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q → _root_.Formalism.IndefR.NX.RealExpansionMajorant B.Q B.Q.cG B.Q.Sx B.Q.nexp ex.nch := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR hTie hDiv hPin
  obtain ⟨jD, eM, hAg, hKs, hSum, hEmb, hLi⟩ := _root_.GlobalTheory.T.lattice_family_adoption_first_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR hTie
  have hLat := _root_.GlobalTheory.T.lattice_family_adoption_second_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR jD eM hTie hAg hSum
  have hTh := _root_.GlobalTheory.T.lattice_family_adoption_third_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR jD eM hDiv hPin hAg hSum
  exact ⟨jD, hAg, ⟨{ eMj := eM, eMj_li := hLi, eMj_lat := hLat, eMj_th := hTh, ks := hKs, eMj_sum := hSum, embW_Ks := hEmb }⟩⟩
end
