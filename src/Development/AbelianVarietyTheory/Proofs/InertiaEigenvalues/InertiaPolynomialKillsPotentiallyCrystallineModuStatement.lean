module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialKillsPotentiallyCrystallineModu
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
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.inertiaPolynomial_kills_potentiallyCrystalline_module : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → ∀ σ : Gw D.nd w, (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → ∀ p : (D.nd.O i)[X], p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (r.comp (decS D.nd w))), ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) • actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e (σ ^ n)) d = 0 := by
  intro D i w hw K' h hN hF hS m r hr hpc σ hσ p hp d hd
  have hPst := GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup
    D i w hw K' h hN hF hS m r hr hpc
  obtain ⟨LL', hL, hV', hchar⟩ :=
    GlobalTheory.T.charPoly_inertia_of_potSemistable_enlargement D i w hw m r hPst
  have hkill := GlobalTheory.T.aeval_inertia_eq_zero_potSemistableDieudonne
    (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.naut.iotaQC i)
    (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ hV' ⟨(σ : GE D.nd), hσ⟩ _
    (hchar σ hσ p hp)
  have hinj : Function.Injective (GlobalTheory.PstLine.incV hL m) := by
    intro x y hxy
    funext j
    exact (IntermediateField.inclusion hL).injective (congrFun hxy j)
  have hd' := GlobalTheory.T.aeval_kills_potCrystalline_of_kills_potSemistable
    (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL LL' h hN hF hS hL
    _ _ (GlobalTheory.PstLine.incV hL m) hinj
    (GlobalTheory.PstLine.isMor_incV (D.nbr i w hw) hL m _) _
    (p.map (D.nbr i w hw).toLL) hkill d hd
  have hsum : ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) •
      (actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw)
        ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e σ) ^ n) d = 0 := by
    rw [GlobalTheory.KillLocal.sumAeval]
    exact hd'
  refine (Finset.sum_congr rfl fun n _ => ?_).trans hsum
  rw [map_pow, GlobalTheory.KillLocal.actPow]
