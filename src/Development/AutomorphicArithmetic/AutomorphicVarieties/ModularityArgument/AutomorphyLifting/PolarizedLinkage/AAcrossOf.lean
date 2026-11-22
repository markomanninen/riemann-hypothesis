module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.QuadFamSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Across
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.BiQuad

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.V.Af.Bc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

private theorem mem_dec_of {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {s : G F Ω}
    (h : ∀ x, s x ∈ A ↔ x ∈ A) : s ∈ Dec (F := F) A := by
  refine mem_Dec.2 (ValuationSubring.ext _ _ fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h ((s⁻¹ : G F Ω) • x), AlgEquiv.smul_def, mul_inv_apply]

private theorem keeps_of_split {K₁ K₂ M Ω : Type} [Field K₁] [Field K₂] [NumberField K₂] [Field M] [NumberField M] [Field Ω] [Algebra ℚ Ω]
    [Algebra K₁ Ω] [Algebra K₂ Ω] [Algebra K₂ M] [Algebra M Ω] [IsScalarTower K₂ M Ω] [IsScalarTower ℚ K₂ Ω] [Algebra ℚ K₁] [IsScalarTower ℚ K₁ Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (hS : SplitIn l K₁ Ω)
    (hM : ∀ s : G K₂ Ω, resG ℚ K₂ Ω s ∈ (resG ℚ K₁ Ω).range → s ∈ (resG K₂ M Ω).range)
    (r : G K₂ Ω →* GL (Fin n) (Qbar l)) : Keeps r M := by
  intro w hw hU A hA
  have hA' : IsPlaceOver A (w.under (𝓞 K₂)) := fun x => by
    rw [IsScalarTower.algebraMap_apply K₂ M Ω]
    exact hA (algebraMap (𝓞 K₂) (𝓞 M) x)
  have hl : A.valuation (l : Ω) < 1 := by
    have h := (hA ((l : ℕ) : 𝓞 M)).2 hw
    simpa using h
  obtain ⟨κ, ⟨g, hg⟩, hne⟩ := hU A hA'
  let ρ : ↥(Dec (F := M) A) →* ↥(Dec (F := K₂) A) :=
    ((AlgEquiv.restrictScalarsHom K₂ : G M Ω →* G K₂ Ω).comp (Dec (F := M) A).subtype).codRestrict _ fun s =>
      mem_dec_of fun x => apply_mem_iff_of_mem_Dec s.2 x
  have hρ : Function.Surjective ρ := by
    intro s
    have hs0 : resG ℚ K₂ Ω s.1 ∈ (resG ℚ K₁ Ω).range := by
      have hd : resG ℚ K₂ Ω s.1 ∈ Dec (F := ℚ) A := mem_dec_of fun x => apply_mem_iff_of_mem_Dec s.2 x
      have hfix := hS A hl _ hd
      exact ⟨AlgEquiv.ofRingEquiv (f := (resG ℚ K₂ Ω s.1).toRingEquiv) hfix, AlgEquiv.ext fun x => rfl⟩
    obtain ⟨t, ht⟩ := hM s.1 hs0
    have hx : ∀ x, t x = s.1 x := fun x => DFunLike.congr_fun ht x
    refine ⟨⟨t, mem_dec_of fun x => ?_⟩, Subtype.ext ht⟩
    rw [hx]
    exact apply_mem_iff_of_mem_Dec s.2 x
  refine ⟨fun i => (κ i).comp ρ, ⟨g, fun s => hg (ρ s)⟩, fun i j e => hne i j (MonoidHom.ext fun s => ?_)⟩
  obtain ⟨t, rfl⟩ := hρ s
  exact DFunLike.congr_fun e t

private theorem step (hFL : FlagLaws) (hUD : AUpDown) (hP : HypothesesH) (hR : RowT) (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K]
    [Field K'] [NumberField K'] [IsCMField K'] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra K' Ω]
    (hK : Module.finrank ℚ K = 2) (hK' : Module.finrank ℚ K' = 2) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hS : SplitIn l K Ω) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (hc : Continuous r) (hA : IsAutomorphicOverImagQuad ι r)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (hθ : IsAlgChar ι θ) (hd : DualTw r θ) (hI : IneAb r) (hF : Flagged r)
    (hi : IsIrr (r.comp ((resG ℚ K Ω).range ⊓ (resG ℚ K' Ω).range).subtype))
    (hW : WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) :
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K' Ω →* G ℚ Ω)) := by
  obtain ⟨M, _, _, _, iK, iK', iM, tK, tK', gK, gK', hs, hs', hM, hM'⟩ := UpperTheory.V.Z.Bc.biQuad K K' Ω hK hK'
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have : IsAlgClosure K' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) M⟩
  have hconj : ∃ c : G ℚ Ω, IsConjEl c := by
    let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
    let : Algebra Ω ℂ := j.toRingHom.toAlgebra
    have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    have : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
    let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
    exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
  obtain ⟨c, hcc⟩ := hconj
  have irrOfRange {Δ Δ' : Type} [Group Δ] [Group Δ']
      (f : Δ →* G ℚ Ω) (f' : Δ' →* G ℚ Ω) (h : ∀ s, ∃ t, f' t = f s)
      (hf : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
    refine ⟨hf.1, fun _ _ _ => trivial, fun W hW hInv => hf.2.2 W hW fun s v hv => ?_⟩
    obtain ⟨t, ht⟩ := h s
    simpa only [MonoidHom.comp_apply, ht] using hInv t v hv
  have pairing {F : Type} [Field F] [CharZero F] [Algebra F Ω] :
      ∃ P, IsPairing c (r.comp (resG ℚ F Ω)) (θ.comp (resG ℚ F Ω)) P := by
    obtain ⟨J, hJ⟩ := hd
    refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
    change resG ℚ F Ω s' = c * resG ℚ F Ω s * c⁻¹ at h
    have e : r c⁻¹ * r (resG ℚ F Ω s') = r (resG ℚ F Ω s) * r c⁻¹ := by
      rw [h, ← map_mul, ← map_mul]
      congr 1
      group
    have e' := congrArg Units.val e
    simp only [Units.val_mul] at e'
    simp only [MonoidHom.comp_apply]
    rw [Units.val_mul, ← Matrix.smul_mul, ← hJ (resG ℚ F Ω s)]
    simp only [Matrix.mul_assoc, e']
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have hiM : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine irrOfRange _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hi
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  have hiM' : IsIrr ((r.comp (resG ℚ K' Ω)).comp (resG K' M Ω)) := he ▸ hiM
  have hiK : IsIrr (r.comp (resG ℚ K Ω)) :=
    irrOfRange ((resG ℚ K Ω).comp (resG K M Ω)) (resG ℚ K Ω) (fun s => ⟨resG K M Ω s, rfl⟩) hiM
  have hiK' : IsIrr (r.comp (resG ℚ K' Ω)) :=
    irrOfRange ((resG ℚ K' Ω).comp (resG K' M Ω)) (resG ℚ K' Ω) (fun s => ⟨resG K' M Ω s, rfl⟩) hiM'
  obtain ⟨P, hPa⟩ := pairing (F := K)
  obtain ⟨P', hPa'⟩ := pairing (F := K')
  have pol : Sol.Pol ι (r.comp (resG ℚ K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P, hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa⟩
  have pol' : Sol.Pol ι (r.comp (resG ℚ K' Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P', hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa'⟩
  have up := (hUD hP hR K M Ω hs l ι n hn (r.comp (resG ℚ K Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K Ω)) hiM pol
    (hA hc K hK hiK) (((hFL ℚ Ω l n r).2.2.2 K).2.1 hF)).1 hW
  rw [he] at up
  exact (hUD hP hR K' M Ω hs' l ι n hn (r.comp (resG ℚ K' Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K' Ω)) hiM' pol'
    (hA hc K' hK' hiK') (((hFL ℚ Ω l n r).2.2.2 K').2.1 hF)).2 (((hFL ℚ Ω l n r).2.2.2 K').1 hI)
    (keeps_of_split hS (fun s h => (hM' s).2 h) _) up

end UpperTheory.V.Z.Win
