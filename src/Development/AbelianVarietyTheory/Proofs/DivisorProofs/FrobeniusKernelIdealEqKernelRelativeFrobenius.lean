module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem frobKerIdeal_le_kerIdeal_relFrob (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    frobKerIdeal p R (G.A n) ≤ kerIdeal ((relFrob h G).app n) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  have ha' : counit (R := R) a = 0 := ha
  have hb : (frobProj h G).app n a ∈ augIdeal R ((frobTwist h G).A n) := by
    change counit (R := R) ((frobProj h G).app n a) = 0
    exact (SemiBialgHom.counit_map ((frobProj h G).app n) a).trans
      ((congrArg (frobRing h) ha').trans (map_zero (frobRing h)))
  change a ^ p ∈ kerIdeal ((relFrob h G).app n)
  rw [← relFrob_app_frobProj h n a]
  exact Ideal.mem_map_of_mem ((relFrob h G).app n).toAlgHom hb

theorem frobKerIdeal_eq_kerIdeal_relFrob (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    frobKerIdeal p R (G.A n) = kerIdeal ((relFrob h G).app n) :=
  le_antisymm (frobKerIdeal_le_kerIdeal_relFrob p R h G n)
    (kerIdeal_relFrob_le_frobKerIdeal p R h G n)

end GlobalTheory.PDiv
