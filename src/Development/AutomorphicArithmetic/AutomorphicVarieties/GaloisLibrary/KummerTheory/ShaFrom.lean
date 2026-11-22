module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open Pointwise

private theorem hom_one {Γ M : Type} [Group Γ] [AddCommGroup M] {f : Γ → M} (hf : ∀ a b, f (a * b) = f a + f b) :
    f 1 = 0 := by
  have := hf 1 1
  rw [one_mul] at this
  exact left_eq_add.1 this

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem zm_triv (D : LData F Ω l) (r : ℕ) (g) (m : ZMod (l ^ r)) : zmTw D r 0 g m = m := by simp [zmTw]

private theorem mem_iff (D : LData F Ω l) (r : ℕ) (z : Z1 (zmTw D r 0)) :
    (Submodule.Quotient.mk z : H1 (zmTw D r 0)) ∈ ShaZm D r 0 ↔
      ∀ v : D.S, ∀ g ∈ Dec (F := F) (D.A v), z.1 (toGS Ω _ g) = 0 := by
  refine (Submodule.mem_iInf _).trans (forall_congr' fun v => ?_)
  refine ((Submodule.Quotient.mk_eq_zero _).trans (mem_coboundaries1 _ _)).trans ⟨fun ⟨m, hm⟩ g hg => ?_, fun h => ⟨0, fun g => ?_⟩⟩
  · exact (hm ⟨g, hg⟩).trans (sub_eq_zero.2 (zm_triv D r _ m))
  · exact (h g.1 g.2).trans (sub_eq_zero.2 (zm_triv D r _ 0)).symm

end
