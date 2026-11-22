module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DownCsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Af
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt := by
  intro hP K L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsol l _ ι n hn r σ hσ hr hpair hirr hI hF hKp haut
  obtain ⟨P, hPr⟩ := hpair
  obtain ⟨j, hj⟩ := hσ
  have algClosure (F : Type) [Field F] [CharZero F] [Algebra F Ω] : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  have : IsAlgClosure K Ω := algClosure K
  have : IsAlgClosure L Ω := algClosure L
  have : IsAlgClosure (maximalRealSubfield K) Ω := algClosure (maximalRealSubfield K)
  let c : G (maximalRealSubfield K) Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))
  have hc : IsConjEl c := ⟨j, hj⟩
  have hpc : IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P := fun s s' hs =>
    hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have halg : IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) := by
    have hcont : Continuous (cycBar (maximalRealSubfield K) Ω l) :=
      _root_.UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont _ Ω l
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP (maximalRealSubfield K) Ω l ι).1 _ (hcont.zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  have hconj (a b : G (maximalRealSubfield K) Ω) (ha : IsConjEl a) (hb : IsConjEl b) :
      (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) a =
        (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) b := by
    have ha' : cycZ (maximalRealSubfield K) Ω l a = -1 :=
      UpperTheory.V.IsConjOm.cyc (E := maximalRealSubfield K) (σ := a.toRingEquiv) ha
    have hb' : cycZ (maximalRealSubfield K) Ω l b = -1 :=
      UpperTheory.V.IsConjOm.cyc (E := maximalRealSubfield K) (σ := b.toRingEquiv) hb
    simp only [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, ha', hb']
  have hN := _root_.UpperTheory.GalN.V.csdN'_alt hP.toClassicalTheorems hn haut
  have hpol : Sol.Pol ι r := ⟨maximalRealSubfield K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, c, P, halg, hconj, hc, hpc⟩
  suffices h0 : AutCsd0 ι r from _root_.UpperTheory.GalN.V.mkCsd'_alt h0 fun hc' => _root_.UpperTheory.V.Z.Win.Dn.down'_alt L hP hsol hn hc' hirr hpol h0.c0 hF hI hKp
    (hN.2 (hc'.comp (continuous_restrictScalarsHom K L Ω)))
  refine _root_.UpperTheory.GalN.V.csdOf0_alt hP (maximalRealSubfield K) K Ω inferInstance l ι n hn r c P hc ?_ hpc
  refine (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hP (maximalRealSubfield K) K L Ω hsol ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ (Or.inr inferInstance)
    l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg hconj ⟨c, P, hc, hpc⟩).2
    ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP L Ω l ι n _).2.2 haut)
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
end
