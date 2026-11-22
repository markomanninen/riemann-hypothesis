module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemOfMemSupportDivCycle

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w u₁ u₂

section Coordinates

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def segreVec (pt : MRingOver o ι →ₐ[o] Ω) : ((k : K) → ι k) → Ω :=
  fun i => ∏ k, pt (X ⟨k, i k⟩)

end Coordinates

section Flags

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Flags

section ProjBundle

variable {K : Type*} [Fintype K]

variable {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section PolyNum

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def monoList {N : ℕ} (mono : Fin N →₀ ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun l => List.replicate (mono l) l

def tupleOfList {α : Type*} [Zero α] {n : ℕ} (L : List α) : Fin n → α := fun j => L.getD j 0

variable {F : Type*} [Field F]

def polyNum (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) {N : ℕ} (cls : Fin N → K → ℤ)
    (Q : MvPolynomial (Fin N) ℤ) (Y : List (K → ℤ)) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * I V n (tupleOfList ((monoList mono).map cls ++ Y))

end PolyNum

section Pairs

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

structure VPair (K : Type*) [Fintype K] (O : Type*) [CommRing O] (ι : K → Type*) [∀ k, Fintype (ι k)] where

  y : K → ℤ

  b : K → ℤ

  f : MRingOver O ι

  g : MRingOver O ι

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def vNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    (p : VPair K O ι) (L : List (K → ℤ)) : ℤ :=
  redEval (fun W => Iκ W n (tupleOfList L)) (divO P p.f p.g)

def monoPairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (ls : List (Fin r)) : ℤ :=
  ∑ k : Fin ls.length, vNum P Iκ n (pr (ls.get k))
    ((ls.take k).map (fun l => (pr l).y - (pr l).b) ++ (ls.drop (k + 1)).map fun l => (pr l).y)

def pairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (Q : MvPolynomial (Fin r) ℤ) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * monoPairNum P Iκ n pr (monoList mono)

variable {Ω : Type*} [Field Ω] [Algebra O Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Pairs

section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

variable {o}





variable (o) in
def genPt (R : Type*) [CommRing R] [IsDomain R] (ι : K → Type*) [∀ k, Fintype (ι k)] :
    MRingOver R ι →ₐ[R] FractionRing (MRingOver R ι) :=
  IsScalarTower.toAlgHom R _ _


section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end DVR

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
