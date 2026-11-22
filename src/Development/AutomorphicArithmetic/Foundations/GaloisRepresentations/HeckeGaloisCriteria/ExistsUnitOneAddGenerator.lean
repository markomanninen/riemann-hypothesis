module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionOfEigenCentralSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfHyp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial
open Formalism.MainNotions.N.PlaceLabelTeichmuller

namespace UpperTheory.GalC

attribute [local instance] GlobalTheory.PassOp.factGk GlobalTheory.PassOp.neZeroGk

theorem exists_unit_one_add_generator (D : D7) (hCen : GlobalTheory.Pass.CentralElt D) (i : D.nd.Loc) :
    ∃ z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))), ∀ F,
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, GlobalTheory.PassOp.prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  refine ⟨z, fun F => ?_⟩
  rw [hz]
  unfold NTypes.onMt
  rw [dite_eq_left (Subalgebra.smul_mem _ hcen _), dite_eq_left hcen, ← LinearMap.smul_apply, ← map_smul]
  rfl

theorem exists_tuple (D : D7) (μ : D.what₂.Tup) (j : ℕ) (F : D.what₂.Mt μ j) (hF : D.ntypes.onMt μ j D.ntypes.e0 F ≠ 0) :
    ∃ s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X], D.ntypes.goodTuple s ∧
      ∀ k v, D.ntypes.onMt μ j (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s k v))) F ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hF
  let ef := fun p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) =>
    fun kv => (⟨ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv))),
      GlobalTheory.CutAtGood.atPlace_mem_center D kv.1 kv.2 _ (D.ntypes.eSer_central kv.1 _)⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))))
  have ht : ∀ p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      tens (fun kv => ESer D kv (p kv)) = ((∏ kv, ef p kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) := by
    intro p
    have hnd := (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).nodup_toList
    have hall : ∀ kv, kv ∈ (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList := fun kv => by simp
    have hprod : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
        ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))).prod =
        ((∏ kv, ef p kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
      have hmap : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
          ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
          ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map (ef p)).map (Subalgebra.val _) := by
        rw [List.map_map]; rfl
      rw [hmap, ← map_list_prod (Subalgebra.val _), ← List.prod_toFinset (ef p) hnd]
      simp
    rw [← hprod]
    have e1 : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
        ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, GlobalTheory.PassOp.prod_plc _ _ hnd]
    congr 1
    funext q
    rw [if_pos (hall q)]
  have he : D.ntypes.e0 = ((∑ p, if goodVec D p then ∏ kv, ef p kv else 0 :
      ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
    rw [e0_eq, eGood, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact ht p
    · rfl
  have onMt_coe (c : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
      D.ntypes.onMt μ j (c : MonoidAlgebra ℂ (G0g D.nd)) = D.ntypes.cenMt μ j c := by
    unfold NTypes.onMt
    rw [dite_eq_left c.2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [he, onMt_coe, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  split_ifs with hg
  · by_contra hc
    obtain ⟨k, v, h0⟩ := hcon (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩)) hg
    apply hc
    rw [← Finset.prod_erase_mul _ (ef p) (Finset.mem_univ ⟨k, v⟩), map_mul, Module.End.mul_apply]
    have hzero : D.ntypes.cenMt μ j (ef p ⟨k, v⟩) F = 0 := by
      rw [← onMt_coe]
      exact h0
    rw [hzero, map_zero]
  · rw [map_zero]; rfl

theorem exists_type (D : D7) (P : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (PI : D.naut.AV i) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X])
    (h1 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0) :
    ∃ τ ∈ P.kty i PI k v, (P.lz k).lab τ = f := by
  classical
  have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
      Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
    intro τ _
    split_ifs
    · exact GlobalTheory.CutAtGood.atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
    · rw [GlobalTheory.CutAtGood.atPlace_zero]
      exact Subalgebra.zero_mem _
  have hsum : D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (∑ τ, ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)) =
      ∑ τ, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)) := by
    let a := fun τ => ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)
    have hco : ∀ τ, a τ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := fun τ => hc τ (Finset.mem_univ _)
    have hcoe (c : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (c : MonoidAlgebra ℂ (G0g D.nd)) =
          D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) c := by
      unfold NTypes.onMt
      rw [dite_eq_left c.2]
    change D.ntypes.onMt _ _ (∑ τ, a τ) = ∑ τ, D.ntypes.onMt _ _ (a τ)
    have hval : (∑ τ, a τ) = ((∑ τ, (⟨a τ, hco τ⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))))) : MonoidAlgebra ℂ (G0g D.nd)) := by
      simp only [AddSubmonoidClass.coe_finsetSum]
    rw [hval, ← AddSubmonoidClass.coe_finsetSum, hcoe, map_sum]
    apply Finset.sum_congr rfl
    intro τ _
    exact (hcoe ⟨a τ, hco τ⟩).symm
  rw [P.eSer_eq k, GlobalTheory.CutAtGood.atPlace_sum, hsum, LinearMap.sum_apply] at h1
  obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hlab : (P.lz k).lab τ = f
  · rw [if_pos hlab] at hτ
    exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
  · exfalso
    apply hτ
    rw [if_neg hlab, GlobalTheory.CutAtGood.atPlace_zero]
    unfold NTypes.onMt
    rw [dite_eq_left (Subalgebra.zero_mem _)]
    have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
    rw [e0, map_zero]
    rfl

theorem tuple_labels {D : D7} {s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]} (hg : D.ntypes.goodTuple s) (i : D.nd.Loc)
    (k : Fin 2) (v : D.nd.PlG k) :
    ((s k v).Monic ∧ (s k v).natDegree = D.R.r ∧ (s k v).coeff 0 ≠ 0) ∧ Squarefree (s k v) ∧
      ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (s k v).IsRoot (u : ZMod (D.host.g k)) := by
  obtain ⟨h1, h2⟩ := hg k
  refine ⟨h1.1 v, h1.2.1 v, fun u hu hr => ?_⟩
  obtain ⟨ℓ, hℓg, hℓ⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  have hℓne : ℓ ≠ D.host.g k := by omega
  have hmem : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ∈
      Formalism.CyclotomicNorms.rootsBar (s k v) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_monic_ne_zero (f := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))) (h1.1 v).1)]
    exact hr.map (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
  rcases hu with rfl | rfl
  · exact h1.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl
  · exact h2.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl

theorem nc_of_type (D : D7) (Q : PairedCharacterCondition.Pend D) (hDZ : PairedCharacterCondition.admDZ Q) (h1 : SumRepresentations.adm1 D) (h0 : SumRepresentations.tie0 D) (i : D.nd.Loc) (PI : D.naut.AV i)
    {s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]} (hg : D.ntypes.goodTuple s)
    (hs : ∀ k v, ∃ τ ∈ Q.kty i PI k v, (Q.lz k).lab τ = s k v) (k : Fin 2) (w : PlE D.host)
    (hw : w ∈ placesOver D.host.E (D.host.g k)) : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locV i PI w) := by
  obtain ⟨v, hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  obtain ⟨τ, hτ, e⟩ := hs k v
  obtain ⟨-, a, b⟩ := tuple_labels hg i k v
  exact UpperTheory.GalS.nc_of_label Q hDZ h1 i k v PI τ hτ (e ▸ a) (e ▸ b) w hv

end UpperTheory.GalC
