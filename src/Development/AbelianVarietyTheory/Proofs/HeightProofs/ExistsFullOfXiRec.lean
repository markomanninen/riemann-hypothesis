module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Formalism.LocalToGlobal.ProjectiveLattices.FullXi
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullDataExtension
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleCharStatement

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.FullExt

theorem exists_full_of_xiRec : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ de, XiRec D p de → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ XiTilde TF.xi de ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  intro D J T hJ hT hc hcan p hp P hP de hde
  obtain ⟨xi, hxi, ht⟩ := GlobalTheory.T.exists_shortSeriesTwistChar_of_twistingIdeleChar D p de hp.own hde
  obtain ⟨dd, TF, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiOK_noVol D J T hJ hT hc hcan p hp P hP xi hxi
  exact ⟨dd, TF, h1, h2, h3, h4 ▸ ht, h5⟩

end GlobalTheory.FinalJoin2.FullExt
