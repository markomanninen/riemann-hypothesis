module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section Lengths

end Lengths

section Models

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def redMap : MRingOver O ι →+* MRingOver (IsLocalRing.ResidueField O) ι :=
  MvPolynomial.map (IsLocalRing.residue O)

def IsModelOver (P : Ideal (MRingOver O ι)) (d : ℕ) : Prop :=
  IsMultiProjPrime P ∧ P.comap (C : O →+* MRingOver O ι) = ⊥ ∧
    ringKrullDim (MRingOver O ι ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

def intCyc {R : Type*} [CommRing R] (Z : Ideal (MRingOver R ι) →₀ ℕ) : Ideal (MRingOver R ι) →₀ ℤ :=
  Finsupp.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero Z

def specCyc (ϖ : O) (P : Ideal (MRingOver O ι)) : Ideal (MRingOver O ι) →₀ ℕ :=
  divCycle P (C ϖ)

def divO (P : Ideal (MRingOver O ι)) (f g : MRingOver O ι) : Ideal (MRingOver O ι) →₀ ℤ :=
  intCyc (divCycle P f) - intCyc (divCycle P g)

def redEval (J : Ideal (MRingOver (IsLocalRing.ResidueField O) ι) → ℤ)
    (Z : Ideal (MRingOver O ι) →₀ ℤ) : ℤ :=
  Z.sum fun W m => m * J (W.map redMap)

end Models


section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]


omit [Fintype K] [IsDomain O] [IsDiscreteValuationRing O] in
theorem isMultiHomog_C (a : O) : IsMultiHomog (C a : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm


end Inhabitants

section LengthInhabitants

open IsLocalRing

end LengthInhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
