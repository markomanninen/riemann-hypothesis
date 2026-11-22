module

public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
public import Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors
public import Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.UG.P

theorem csBdd_nat_mul {K : Type} [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : 𝓞 K, (m : 𝓞 K) = d * t := by
  classical
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
    exact ⟨t, by rw [← ht, mul_comm]⟩

theorem class_set_finite_bounded_holds (hCovolOfDual : Formalism.UG.CS.CovolOfDual) :
    Formalism.UG.CS.ClassSetFiniteBdd := by
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos d e hd he
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.traceReal_main h hsymm hpos
  obtain ⟨C, hC⟩ := hCovolOfDual K V h hsymm hpos N ι hι e he
  obtain ⟨m, hm, t, ht⟩ := csBdd_nat_mul d hd
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M)}
  have hfull : ∀ M ∈ S, Submodule.IsFullLattice K M := by
    intro M hM
    let W := Submodule.span K (M : Set V)
    let b := Module.finBasis K W
    let f : V →ₗ[K] (Fin (Module.finrank K W) → K) := LinearMap.pi (fun i => h (b i : V))
    have hf : Function.Injective f := by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hzero : (h.flip x).comp W.subtype = 0 := by
        apply b.ext
        intro i
        exact congrFun (LinearMap.mem_ker.mp hx) i
      have hz (y : V) (hy : y ∈ M) : h y x = 0 :=
        LinearMap.congr_fun hzero ⟨y, Submodule.subset_span hy⟩
      have hxd : x ∈ Formalism.HermitianLatticesTheory.dual h M := by
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf,
          Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        rw [hz y hy]
        exact Submodule.zero_mem _
      -- The dual bound puts a nonzero scalar multiple of x in M, so positivity forces x = 0.
      have hxx := hsymm.eq_iff.mp (hz _ (hM.2.2 x hxd))
      rw [map_smul, smul_eq_mul] at hxx
      have heK : (e : K) ≠ 0 := fun he0 => he (RingOfIntegers.ext he0)
      have hxx0 := (mul_eq_zero.mp hxx).resolve_left heK
      by_contra hx0
      simpa [hxx0] using hpos x hx0
    have hdim := LinearMap.finrank_le_finrank_of_injective hf
    exact { hM.1 with
      span_eq_top := Submodule.eq_of_le_of_finrank_le le_top
        (by simpa only [finrank_top, Module.finrank_fin_fun] using hdim) }
  have hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M, (m : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro M hM x hx y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hM.2.1 x hx y hy)
    refine Submodule.mem_one.mpr ⟨t * a, ?_⟩
    have hmK : (m : K) = (d : K) * (t : K) := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      simpa using this
    rw [map_mul, ha, hmK]
    have htc : algebraMap (𝓞 K) K t = (t : K) := rfl
    rw [htc]
    ring
  obtain ⟨s, -, hs⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.shortVectors
    Formalism.HermitianLatticesTheory.finIntermediate Formalism.HermitianLatticesTheory.isomOfTrace h hpos N ι hι hmul m hm C S hSd
    (fun M hM => hlat M (hfull M hM)) (fun M hM _ _ => hC M hM.1 hM.2.2)
  exact ⟨s, fun M hM hdM heM => hs M ⟨hM, hdM, heM⟩⟩

end Formalism.UG.P
