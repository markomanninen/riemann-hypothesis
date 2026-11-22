module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfAdmissibility
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducibleAltBis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAllStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement

@[expose] public section

namespace PositivityTheory.Exh

theorem lUnlinkedIrr_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : GlobalTheory.BZSeg.LUnlinkedIrr k :=
  GlobalTheory.T.lUnlinkedIrr_of_irreducibleAdmissible k irreducibleAdmissibleGL (GlobalTheory.T.segment_jacquet_all irreducibleAdmissibleGL hZ) (fun k _ _ _ _ => (geometricLemmaGL k).1)
    (GlobalTheory.CompanionTheory.BZNuPair.nuPair k irreducibleAdmissibleGL) (GlobalTheory.T.whittaker_rank_standard_of_heredity k (GlobalTheory.T.whittaker_heredity k) (PositivityTheory.rg.gu.whit.whitRankIrr k))
    fun _ _ x hd => GlobalTheory.T.product_irreducible_finite_length irreducibleAdmissibleGL x hd

end PositivityTheory.Exh
