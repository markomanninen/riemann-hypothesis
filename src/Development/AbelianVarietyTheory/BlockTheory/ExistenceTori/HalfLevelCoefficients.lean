module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.DatumOfRecordSignature
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

structure IsHalf (D : D7) (Mb : Ideal (𝓞 D.host.E)) : Prop where
  fromK : Mb = Ideal.span {a | a ∈ Mb ∧ a ∈ Algebra.adjoin ℤ {w0E D}}
  prod : Mb * Mb.map (bH D) = Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}
  coprime : Mb ⊔ Mb.map (bH D) = ⊤

theorem three_le_g (D : D7) (k : Fin 2) : 3 ≤ D.host.g k := by
  have := (D.host.g_prime k).two_le
  have := g_ne_two D k
  omega

def levelAt (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Level (hostOfRecord D) where
  M := D.host.g 0 * D.host.g 1
  three_le := by
    have := three_le_g D 0
    have := three_le_g D 1
    nlinarith
  odd := ((D.host.g_prime 0).odd_of_ne_two (g_ne_two D 0)).mul ((D.host.g_prime 1).odd_of_ne_two (g_ne_two D 1))
  Mb := Mb
  fromK := h.fromK
  prod := h.prod
  coprime := h.coprime
  A := 1
  A_pos := Nat.one_pos


def PrimesOver (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal

def halfOf (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Ideal (𝓞 D.host.E) :=
  ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients
