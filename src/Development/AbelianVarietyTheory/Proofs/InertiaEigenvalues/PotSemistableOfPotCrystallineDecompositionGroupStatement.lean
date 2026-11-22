module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlargeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficieStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) := by
  first | exact @GlobalTheory.PstOfCrys.pst_of_pc | exact GlobalTheory.PstOfCrys.pst_of_pc | (intros; apply GlobalTheory.PstOfCrys.pst_of_pc <;> assumption)
