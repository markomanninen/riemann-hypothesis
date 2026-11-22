module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
public import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSmulMemOfMemLocW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChainHost
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTopRowSym
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.StdModel

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

section Ker

variable {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}

theorem stdKer_iff (t : KerEntTied ex) : I.StdKer l Z t ↔ I.StdKerTie l Z t :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩⟩

end Ker

section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

end Tw




section Frames

open GlobalTheory.Mem.FormSym


end Frames

end GlobalTheory.Mem.Col2.StdModel

end
