module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.IP

theorem eulerRight_of_unramifiedDoubling : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ D : D7, GlobalTheory.Core.Rk.IP.EulerRight D := by
  intro p2 p6 D
  have hU := GlobalTheory.InertZeta.unramDoublingInert
  have hPBi : ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := GlobalTheory.T.sphericalParameterBound_nonsplit_places hU D
  have hPB : ParamBoundOn D (fun _ => True) := by
    intro A L hL v _
    by_cases h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.Core.Rk.BdSplit.paramBound_split D A L hL v h
    · exact hPBi A L hL v h
  have hLZ : LocalZetaOn D (fun _ => True) := by
    intro A L hL χ b hχ hr v _
    by_cases h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.Core.Rk.IP.localZetaOn_split p6 D A L hL χ b hχ hr v h
    · exact GlobalTheory.LocZetaInertAd.localZetaOn_inert hU D hPBi A L hL χ b hχ hr v h
  exact GlobalTheory.Core.Rk.EulerProd.eulerRight p2 D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair GlobalTheory.weilRepresentationUnitaryPair D) hLZ hPB

end GlobalTheory.Core.Rk.IP
