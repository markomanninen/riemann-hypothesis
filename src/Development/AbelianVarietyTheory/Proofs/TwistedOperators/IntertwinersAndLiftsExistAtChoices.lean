module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChainStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChainStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepThetaLiftsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLiftStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExThOfChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMapStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicitySpaceThetaMapOfRapidDecayStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModelsStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExAtAssembly

theorem exAt_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → HostHyp D → R.IsChainW → R.IsThPW → R.ExAt := by
  intro h1 h2 h3 h4 D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr hH hc hp
  have eP : R.ex_ioP := GlobalTheory.T.exists_lowestKType_coeffSpace_fockMap D G Pl0 T A Ks R h0 hf hm hp.ωP hp.vP
  have eF : R.ex_thF := GlobalTheory.T.exists_multiplicitySpaceThetaMap_of_rapidDecay h3 D G Pl0 T A Ks R h0 hf hm hp eP
  exact ⟨GlobalTheory.T.exists_innerStepIntertwiners_thetaChain h1 h2 D G Pl0 T A Ks R h0 hf hm hH hc, GlobalTheory.T.exists_lastStep_intertwiner_chain D G Pl0 T A Ks R h0 hf hm hc,
    GlobalTheory.T.exists_innerStepThetaLifts h1 h2 h3 h4 D G Pl0 T A Ks R h0 hf hm hH hc, GlobalTheory.T.exists_lastStep_thetaLift D G Pl0 T A Ks R h0 hf hm hc,
    GlobalTheory.ProjectedLift.ex_Th_of_chain D G Pl0 T A Ks R h0 hf hm hr, eP, eF,
    GlobalTheory.T.exists_thetaLift_goodProjector_models D G Pl0 T A Ks R h0 hf hm hp.thF eF⟩

end GlobalTheory.ExAtAssembly
