module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RecPair

theorem coe_eq_of_frame {D : D7} {V : HSp D} {β} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSDFrame V β Λ 1) : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  exact Set.ext fun x => ⟨h2 x, h1 x⟩

theorem selfDual_of_coe {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V) : IsSelfDualC V Λ := by
  obtain rfl : Λ = GlobalTheory.PlaceModel.latFrame V := SetLike.coe_injective (h.trans (GlobalTheory.PlaceModel.coe_latFrame V).symm)
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem under_ne {D : D7} {e : Formalism.L2.Theta.AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e P) {v ε}
    (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : P.under (𝓞 D.host.F) ≠ v := by
  intro hP
  obtain ⟨w, hw, -, hc⟩ := GlobalTheory.RepsCompare.exists_splitAt_of_isIdemAt h
  obtain rfl : w = v := HeightOneSpectrum.ext (hc.symm.trans (congrArg HeightOneSpectrum.asIdeal hP))
  obtain ⟨⟨α, rfl, h3, h4⟩, hn⟩ := hv
  have : α = singleV D.host.F w 1 := GlobalTheory.SplitIdem.af_ext _ fun u => by
    by_cases hu : u = w
    · subst hu; rw [h3, GlobalTheory.LatVac.evalV_singleV_same]
    · rw [h4 u hu, GlobalTheory.LatVac.evalV_singleV_ne _ w _ hu]
  subst this
  exact hn ⟨e, h.1, hw.2.2⟩

theorem exp_mu {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) (t : T0) (τ : D.what₂.Tau) :
    ∃ a : ℤ, HasInfExp D (L.mu t ((i : ℕ) + 1)) τ a := by
  have h1 : HasInfExp D (L.mu0 ((i : ℕ) + 1)) τ (-(D.hc τ).e i) := by
    obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
    refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => -(D.hc τ).e i) (hL.mu0 i)
      ⟨fun τ => n (D.eTau τ), fun τ => ?_, fun k => ?_⟩ τ
    · simp only [hn, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]
    · rw [hi k]
      exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
        ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm
  have h2 : HasInfExp D (L.xi t) τ 0 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    have := D.host.isCMField_hostE
    refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t) ⟨fun _ => 0, fun _ => by norm_num, fun k => ?_⟩ τ
    rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho k]
    simp
  obtain ⟨z, hz⟩ := (D.hc τ).e_int i
  refine ⟨-z, ?_⟩
  have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul h1 h2
  rw [hz, add_zero, ← Int.cast_neg] at h3
  exact h3

end GlobalTheory.AdTh.RecPair
