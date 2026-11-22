module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalKillsPotCrystallineOfKillsPotSemistable
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
theorem _root_.GlobalTheory.T.aeval_kills_potCrystalline_of_kills_potSemistable : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L L' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (hL : L.1 ≤ L'.1) {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V'] (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V') (f : V →ₗ[ℚ_[l]] V'), Function.Injective f → GlobalTheory.PstLine.IsMor hL f ρ ρ' → ∀ (g : ↥(GK K)) (q : (↥L.1)[X]), (∀ y ∈ GlobalTheory.Pst.Dpst P ρ', Polynomial.aeval (GlobalTheory.Pst.stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom) y = 0) → ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, Polynomial.aeval (actVB (P.PD K) ρ g) q d = 0 := by
  first | exact @GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst | exact GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst | (intros; apply GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst <;> assumption)
