module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ToNewform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af
open scoped Matrix

private theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

private theorem cls_frob {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N]
    {A : ValuationSubring Ω} (hN : ¬ A.valuation (N : Ω) < 1) {q : ℕ} {σ : G ℚ Ω} (hσ : IsFrob A q σ) :
    ((Chr.cls ℚ Ω N σ : (ZMod N)ˣ) : ZMod N) = q := by
  obtain ⟨-, -, -, -, -, -, hpow, -⟩ := ML.placeBasic Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h2 : σ ζ = ζ ^ q := hpow A _ N _ hσ hN ζ hζ.pow_eq_one
  rw [Chr.cls_spec N σ ζ hζ.pow_eq_one, pow_eq_pow_mod q hζ.pow_eq_one] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos N)) h2
  rw [← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω N σ : (ZMod N)ˣ) : ZMod N), h3, ZMod.natCast_mod]
