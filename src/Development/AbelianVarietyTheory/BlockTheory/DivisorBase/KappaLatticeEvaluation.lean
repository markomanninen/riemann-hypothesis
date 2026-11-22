module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section Generic

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R]

def latIn (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) : Submodule (𝓞 K) R :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_latIn (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (f : R) :
    f ∈ latIn C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f := by
  unfold latIn latOf
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F.2, hF⟩
  · rintro ⟨hC, hv⟩
    exact ⟨⟨f, hC⟩, hv, rfl⟩

end Generic

variable {D : D7}

abbrev cuspW (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.cuspA j (wtA w) w.n

def supLat (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule (𝓞 T.Q.c.F) (T.R j) :=
  latIn (cuspW T j w) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) isVal_valSet

def FullAt (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Prop :=
  (supLat T j w).FG ∧ Submodule.span T.Q.c.F (supLat T j w : Set (T.R j)) = cuspW T j w

end GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation
