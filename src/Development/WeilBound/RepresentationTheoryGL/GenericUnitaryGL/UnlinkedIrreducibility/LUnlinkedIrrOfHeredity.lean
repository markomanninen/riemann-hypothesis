module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerRankHeredity.ProdFL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdQuotGenericOfStdSubGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairIrreducibleUnlinked
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiProdCompInvTranspose
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducibleAltBis
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

@[expose] public section

noncomputable section

namespace GlobalTheory.RgGu.Unl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitRankStd : GlobalTheory.BZSeg.WhitRankStd k :=
  GlobalTheory.T.whittaker_rank_standard_of_heredity k (GlobalTheory.T.whittaker_heredity k) (PositivityTheory.rg.gu.whit.whitRankIrr k)

theorem lUnlinkedIrr_nu (hJ : Zc.LSegJacquet k) (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hN : GlobalTheory.BZSeg.NuPair k) :
    GlobalTheory.BZSeg.LUnlinkedIrr k := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := by
    first
    | exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    | exact PositivityTheory.Exh.irreducibleAdmissibleGL
    | exact GlobalTheory.RgGu.irreducibleAdmissibleGL
  have hF : GlobalTheory.BZSeg.ProdIrrFiniteLength k := by
    first
    | exact GlobalTheory.RgGu.prodIrrFiniteLength k
    | exact fun h N x hd => GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  exact GlobalTheory.T.lUnlinkedIrr_of_irreducibleAdmissible k hA hJ hG hN (whitRankStd k) hF

theorem lUnlinkedComm_of_irr (hL : GlobalTheory.BZSeg.LUnlinkedIrr k) : GlobalTheory.BZSeg.LUnlinkedComm k :=
  GlobalTheory.T.unlinked_commute_of_irreducible k GlobalTheory.RgGu.irreducibleAdmissibleGL hL

end GlobalTheory.RgGu.Unl

end
