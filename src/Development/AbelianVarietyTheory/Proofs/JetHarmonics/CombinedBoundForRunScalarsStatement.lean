module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CombinedBoundForRunScalars
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
public import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
public import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combinedBound_for_runScalars : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), GlobalTheory.PtTie.Oriented T EX → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → CombBound G (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (cc D large₂ C2 A2 7 wL) (nusR h j wL) ∧ 0 < (cc D large₂ C2 A2 7 wL) := by
  first | exact @GlobalTheory.RunJoin.combBound_run | exact GlobalTheory.RunJoin.combBound_run | (intros; apply GlobalTheory.RunJoin.combBound_run <;> assumption)
