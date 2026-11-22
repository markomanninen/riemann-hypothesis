module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRowsStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.OPinAt

theorem mtInput_mtL {D : D7} (L : LocAll (lay0 D)) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (h : MtInput D M tup Q) : MtInput (withLoc L) (mtL L M) tup Q :=
  ⟨h.prod, h.para, h.uni, h.hyp, h.wt, h.rat, h.int, h.full⟩

theorem classSum_loc_of_sumTw {D : D7} {M : MtFam D} (h : SumTw D M) (i : D.nd.Loc) :
    GlobalTheory.CoefDuty.ClassSum (M.loc i) := by
  have e := D.nd.mu_w i
  have hs := h (D.nd.w i) (D.nd.w_tw i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2
  unfold MtFam.loc
  rw [e]
  exact hs

end GlobalTheory.HeightCounting.Up.OPinAt


end
