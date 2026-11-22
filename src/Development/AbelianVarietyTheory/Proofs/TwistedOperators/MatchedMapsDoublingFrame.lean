module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizersFixVacuaFixesPureTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutUnitaryPointStabilizesLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedOfFixesPureTensorsVacuaOutsideStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepListProdDistinctPlacesPureTensorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointDarbouxTrivialArchimedeanStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
open scoped Classical
namespace GlobalTheory.PlacePureFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

theorem side {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (om : Rep σ Y Wd) (h : UA σ Wd.J)
    (hloc : ∀ v, ∀ hh ∈ UAt σ Wd (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, hh)) φ φ₁)
    (S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)))
    (hfix : ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₀ ⊆ S →
      (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u * e = 0) →
      (∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * e = 0 ∨ u * e = u) →
      ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
        om (1, loc e he h) (pure f φ) = pure f φ)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
      (∀ v, Acts (evFin F v) (om (1, loc (idem F v) (idem_mul_self v) h)) (φ v) (φ₁ v)) ∧
      om (1, h) (pure f φ) = pure f φ₁ := by
  have hvAt : ∀ v, loc (idem F v) (idem_mul_self v) h ∈ UAt σ Wd (evFin F v) := by
    intro v u hu
    show u • (mat (loc (idem F v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  choose φ₁ hφ₁SB hφ₁Act using fun v => hloc v _ (hvAt v) (φ v) (hSB v)
  have hN : {v | ¬ φ v = M.vac v}.Finite := hvac
  have hN2 : {v | ¬ M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite := hM.std
  set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) := S₀ ∪ hN.toFinset ∪ hN2.toFinset with hSdef
  have hS₀ : S₀ ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hφS : ∀ w ∉ S, φ w = M.vac w := fun w hw => by
    by_contra hc; exact hw (Finset.mem_union_left _ (Finset.mem_union_right _ (hN.mem_toFinset.2 hc)))
  have hvacS : ∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := fun w hw => by
    by_contra hc; exact hw (Finset.mem_union_right _ (hN2.mem_toFinset.2 hc))
  have hidem_at : ∀ w v (u : AF F), At (evFin F w) u → w ≠ v → u * idem F v = 0 := by
    intro w v u hu hwv
    apply mul_idem_of_evFin
    rw [← idem_mul_of_at hu, map_mul, evFin_idem, if_neg (Ne.symm hwv), zero_mul]
  have key : ∀ v ∉ S, φ₁ v = φ v := by
    intro v hv
    have hA := hφ₁Act v
    rw [hφS v hv] at hA ⊢
    refine GlobalTheory.T.vacuum_fixed_of_fixes_pureTensors_vacuaOutside F E σ M om v _ S (hM.vac v).1 hvacS (fun f' φ' hSB' hout => ?_) (φ₁ v) hA
    refine hfix S (idem F v) (idem_mul_self v) hS₀ (fun w hw u hu => hidem_at w v u hu (fun e => hv (e ▸ hw)))
      (fun w _ u hu => ?_) f' φ' hSB' hout
    by_cases hwv : w = v
    · subst hwv; right; rw [mul_comm]; exact idem_mul_of_at hu
    · left; exact hidem_at w v u hu hwv
  refine ⟨φ₁, hφ₁SB, ?_, hφ₁Act, ?_⟩
  · filter_upwards [hvac, S.eventually_cofinite_notMem] with v hv hvS
    rw [key v hvS, hv]
  · have heS : idemS F S * idemS F S = idemS F S := idemS_mul_self S
    have heS' : (1 - idemS F S) * (1 - idemS F S) = 1 - idemS F S := by
      rw [sub_mul, one_mul, mul_sub, mul_one, heS, sub_self, sub_zero]
    have horth : idemS F S * (1 - idemS F S) = 0 := by rw [mul_sub, mul_one, heS, sub_self]
    have hdec : h = (S.toList.map fun v => loc (idem F v) (idem_mul_self v) h).prod * loc (1 - idemS F S) heS' h := by
      apply ua_ext
      rw [mat_mul, mat_prod_loc h _ S.nodup_toList, Finset.toList_toFinset, mat_loc, phi_mul_orth horth,
        add_sub_cancel, phi_one]
    have hnot : ∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * idemS F S = 0 := by
      intro w hw u hu
      rw [← idem_mul_of_at hu, mul_comm (idem F w), mul_assoc, idem_mul_idemS_of_notMem hw, mul_zero]
    have hk : om (1, loc (1 - idemS F S) heS' h) (pure f φ) = pure f φ := by
      refine hfix S _ heS' hS₀ (fun w hw u hu => ?_) (fun w hw u hu => Or.inr ?_) f φ hSB hφS
      · calc u * (1 - idemS F S) = (idem F w * u) * (1 - idemS F S) := by rw [idem_mul_of_at hu]
          _ = u * (idem F w - idem F w * idemS F S) := by ring
          _ = 0 := by rw [idem_mul_idemS_of_mem hw, sub_self, mul_zero]
      · rw [mul_sub, mul_one, hnot w hw u hu, sub_zero]
    have hmul : ∀ (a b : UA σ Wd.J) (x : (Fin n × Fin d → AF F) → ℂ), om (1, a * b) x = om (1, a) (om (1, b) x) := by
      intro a b x
      have : ((1 : UA σ Y.J), a * b) = (1, a) * (1, b) := by simp
      rw [this, map_mul]; rfl
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hvac.and hM.std).mono fun v hv => hv.1.trans hv.2
    conv_lhs => rw [hdec]
    rw [hmul, hk, GlobalTheory.T.weilRep_list_prod_distinctPlaces_pureTensor F E σ om (fun v => loc (idem F v) (idem_mul_self v) h) φ φ₁ hSB hφ₁SB hφ₁Act hstd S.toList
      S.nodup_toList f]
    congr 1
    funext v
    by_cases hv : v ∈ S
    · rw [if_pos (Finset.mem_toList.2 hv)]
    · rw [if_neg (mt Finset.mem_toList.1 hv), key v hv]

end GlobalTheory.PlacePureFin
end
