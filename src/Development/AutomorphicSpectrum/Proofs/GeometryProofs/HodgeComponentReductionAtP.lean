module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_V_inr_iff_latOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inr τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hF hpS τ σ hσ s q hs hq e
  have hp : p.Prime := Fact.out
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' q → p' = p := by
    intro r hrS hrq
    by_contra hne
    have hloc : IsLocalRing (regAt 𝔐.ξ q) :=
      IsLocalRing.of_surjective' (genMap 𝔐.ξ q).rangeRestrict
        (genMap 𝔐.ξ q).rangeRestrict_surjective
    have key : ∀ m : ℕ, InFibre 𝔐.ξ m q → ¬ IsUnit ((m : regAt 𝔐.ξ q)) := by
      intro m hm hu
      apply hm
      obtain ⟨u, hu'⟩ := hu
      have h1 : (m : Ω) * (((u⁻¹ : (regAt 𝔐.ξ q)ˣ) : regAt 𝔐.ξ q) : Ω) = 1 := by
        have h2 := congrArg (fun x : regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
        simpa [hu'] using h2
      have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
      refine ⟨h0, natCast_mem _ m, ?_⟩
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    have hcop : Nat.Coprime r p := (Nat.coprime_primes (𝔐.S_prime r hrS) hp).2 hne
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (regAt 𝔐.ξ q))
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
    · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)
  have hV : 𝔐.V (Sum.inr τ) q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inr τ)) q := by
    unfold HodgeCpt.V
    rw [Lat.patch_of_unique _ _ _ hpS hq hu]
    rfl
  have hσ' : ∀ a : 𝓞 E, 𝔐.emb (Sum.inr τ) a = (σ.comp (cmConj E).toRingHom) (a : E) := by
    intro a
    have h1 : 𝔐.emb (Sum.inr τ) a = 𝔐.emb (Sum.inl τ) (H.bar a) := rfl
    rw [h1, ← hσ, H.bar_eq]
    rfl
  have hom := hF.om'_loc s q hs hq
  rw [hV, LieModel.mem_htDual_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, fun w hw => ?_⟩
    · have := (Submodule.mem_iInf _).mp h1 a
      rw [← hσ' a]
      simpa [sub_eq_zero] using this
    · rw [one_mul]
      refine h2 w ?_
      have : w ∈ HT.omP 𝔐 p q := by
        rw [hom]
        exact Submodule.subset_span hw
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨(Submodule.mem_iInf _).mpr fun a => ?_, fun w hw => ?_⟩
    · have := HT.LatBasic.mem_eigSp.1 h1 a
      rw [← hσ' a] at this
      simpa [sub_eq_zero] using this
    · have hw' : w ∈ HT.omP 𝔐 p q := hw
      rw [hom] at hw'
      clear hw
      induction hw' using Submodule.span_induction with
      | mem x hx => simpa using h2 x hx
      | zero => simpa using (regAt 𝔐.ξ q).zero_mem
      | add x y _ _ hx hy => simpa using (regAt 𝔐.ξ q).add_mem hx hy
      | smul c x _ hx =>
        have : (c • x) e = (c : Ω) * x e := rfl
        rw [this]
        exact (regAt 𝔐.ξ q).mul_mem c.2 hx

end GlobalTheory.CompanionTheory.Ar.Flat
