module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ContinuousOnThetaCFunLtr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.TestFun
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.MirGen
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SgOneHd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLawStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeightsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLawsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLawStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLawStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroupStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLawStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLawStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDetStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDetStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviQuotientOfBlockDetStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDetStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGalleryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGoodStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionaryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionaryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGoodStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativityStatement
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorisationHolomorphic

@[expose] public section

noncomputable section

namespace PositivityTheory.RgEis.Hd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem idTube : IdTube := GlobalTheory.T.identity_tube_holds
theorem tubeChain : TubeChain := GlobalTheory.T.tube_chain_holds
theorem secLaw : SecLaw := GlobalTheory.T.section_law_holds
theorem htLip : HtLip := GlobalTheory.T.height_lipschitz_holds
theorem stage : PiLocalization₂ := GlobalTheory.T.staged_estimate_holds
theorem wallLaw_of : SecLaw → WallLaw := GlobalTheory.T.wall_law_of_section_law
theorem cross_of : SecLaw → HtLip → PiLocalization₂ → WallLaw → Cross := GlobalTheory.T.crossing_of_walls_and_heights
theorem gallery_of : SecLaw → IdTube → TubeChain → Cross → Gallery := GlobalTheory.T.gallery_of_tubes_and_crossing
theorem transfer_of : SecLaw → WallLaw → Transfer := GlobalTheory.T.transfer_of_section_and_wall_laws
theorem twist_of : SecLaw → Twist := GlobalTheory.T.twist_of_section_law
theorem scale : Scale := GlobalTheory.T.eisenstein_scaling_law
theorem grpTop : GrpTop := GlobalTheory.T.general_linear_topological_group
theorem bdetLaw : BdetLaw := GlobalTheory.T.block_determinant_law
theorem extLaw : ExtLaw := GlobalTheory.T.extension_law
theorem parLaw_of : BdetLaw → ExtLaw → GrpTop → ParLaw := GlobalTheory.T.parabolic_law_of_block_det
theorem leviS_of : BdetLaw → ExtLaw → GrpTop → LeviS := GlobalTheory.T.levi_decomp_of_block_det
theorem leviQ_of : BdetLaw → ExtLaw → GrpTop → LeviQ := GlobalTheory.T.levi_quotient_of_block_det
theorem convGrOf_of : BdetLaw → ExtLaw → ConvGrOf := GlobalTheory.T.convergence_group_of_block_det
theorem convU_of : ParLaw → ConvU := GlobalTheory.T.unipotent_convergence_of_parabolic
theorem sgStep_of : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := GlobalTheory.T.siegel_induction_from_gallery
theorem epConv : EpConv := GlobalTheory.CompanionTheory.EpConvB.epConv
theorem epMain_of : EpConv → EpMain := GlobalTheory.CompanionTheory.EpsteinMain.Hd.epMain_of_epConv
theorem testFun : TestFun := PositivityTheory.RgEis.TF.testFun
theorem testSph : TestSph := GlobalTheory.T.spherical_test_function_exists
theorem stdGood : StdGood := GlobalTheory.T.standard_section_good
theorem mirGen_of : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen := PositivityTheory.RgEis.MG.mirGen
theorem dict : Dict := GlobalTheory.T.local_global_dictionary
theorem dictInf : DictInf := GlobalTheory.T.archimedean_local_global_dictionary
theorem cmGood_of : StdGood → Dict → DictInf → CMGood := GlobalTheory.T.constant_multiplier_good
theorem cmMir_of : Dict → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → MirGen → CMMir := GlobalTheory.T.constant_multiplier_mirabolic
theorem sgOne_of : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := PositivityTheory.RgEis.So.sgOne_hd
theorem siegelMult_of : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    SiegelEisensteinSeries.BRoad.SiegelMult := GlobalTheory.T.siegel_eisenstein_multiplicativity

theorem sgAll_of (hG : CMGood) (hM : CMMir) (h1 : SgOne) (hS : SgStep) : SgAll := by
  intro F E _ _ _ _ _ σ χ c h h' hχ hc ε
  suffices H : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → 1 ≤ n → (adCM σ χ).Sg ε ι from
    fun ι _ _ hι => H _ ι rfl hι
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hι hn
    rcases Nat.eq_or_lt_of_le hn with e | e
    · exact h1 F E σ χ c h h' hχ hc ε ι (hι.trans e.symm)
    · exact hS E _ (adCM σ χ) (hG F E σ χ c h h' hχ hc) (hM F E σ χ c h h' hχ hc) ε ι (by omega)
        fun κ _ _ h1 h2 => ih _ (hι ▸ h2) κ rfl h1

theorem sgAll : SgAll :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
    (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
    (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
      (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
      (convGrOf_of bdetLaw extLaw) (convU_of hP))

theorem eisBL : GlobalTheory.ThK.Dbl.EisBL :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  SiegelEisensteinSeries.BRoad.eisBL_of GlobalTheory.T.eisenstein_half_holds
    (siegelMult_of secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation

end PositivityTheory.RgEis.Hd
