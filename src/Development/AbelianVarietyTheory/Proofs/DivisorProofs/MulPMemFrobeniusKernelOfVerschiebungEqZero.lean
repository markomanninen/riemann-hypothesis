module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega

@[expose] public section

set_option autoImplicit false

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_of_verschiebung_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1) (ha : (verschiebung h G).app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  let f := (G.mulP 1).comp ((relFrob h G).app 1)
  let K := kerIdeal f
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff f x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp ((relFrob h G).app 2 : (frobTwist h G).A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal (R := R) (A := (frobTwist h G).A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff (mulBy R ((frobTwist h G).A 2) p) y).2 fun z => by
      change x ((relFrob h G).app 2 (mulBy R ((frobTwist h G).A 2) p z)) = _
      rw [← (frobTwist h G).mulP_res 1 z, PDivGroup.app_mulP (relFrob h G)]
      simpa only [f, BialgHom.coe_comp, Function.comp_apply, CoalgHomClass.counit_comp_apply]
        using hx ((frobTwist h G).res 1 z)
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app (verschiebung h G)] at ha
  have hb : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) p := by
    have : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) (p ^ 1) := by
      rw [← (frobTwist h G).ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x ((relFrob h G).app 2 ((verschiebung h G).app 2 b)) = 0 := hy hb
  rw [relFrob_app_verschiebung_app] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup
