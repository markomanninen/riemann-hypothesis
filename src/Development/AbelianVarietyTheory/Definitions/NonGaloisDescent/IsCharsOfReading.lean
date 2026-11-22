module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd

@[expose] public section

noncomputable section

namespace GlobalTheory.Triple.Model

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open scoped TensorProduct

variable {D : D7}

section Indep

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool}

theorem notMem_l {k : Fin 2} (hk : X.l i ≠ D.host.g k) (v : D.nd.PlG k) :
    ((X.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal :=
  GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) (X.lPrime i).out hk.symm (D.naut.plGw_over k v)

end Indep

section Tame

variable (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om)

variable {C art}

end Tame

section Record

variable (D) (C : CharFrame D) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} (ha : IsGlobalArtin art) (hC : ValLL0 D C)
  (hs : ∀ x : ↥D.LL0, star (x : D.what₂.LL) ∈ D.LL0)

def rd (i : D.ntw.Tw) : Reading D.ntw i true := (Reading.nonempty i true).some



structure Chars (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) (i : D.ntw.Tw) where
  delta : GalE D →* (D.ntw.O0 i)ˣ
  chi1 : ℕ → Bool → (GalE D →* (D.ntw.O0 i)ˣ)
  gal : ∀ (j : Fin D.R.m) (b : Bool), ∃ n, IsGal art (rd D i).κ (GlobalTheory.GalChar.sideIso (rd D i).ι b)
    (blockChar C (D.ntw.l i) j) n (chi1 (j.1 + 1) b)
  h1 : IsOpen (delta.ker : Set (GalE D))
  h2 : AntiHom D.ntw.cc delta
  h3 : RamExactly delta ↑(D.ntw.pD i)
  h4 : ∀ v ∈ D.ntw.pD i, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    Nat.card ((Ine (F := D.host.E) A).map delta) = 15
  h5 : ∀ j b, Continuous (fun g => ((chi1 j b g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))
  h6 : ∀ j b v, v ∉ placesOver D.host.E (D.ntw.l i) → (∀ k, v ∉ placesOver D.host.E (D.host.g k)) → v ∉ D.ntw.pD i →
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ = 1
  h7 : ∀ j b, ∀ v ∈ D.ntw.pD i, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ = if b then delta σ else (delta σ)⁻¹
  h8 : ∀ j b k v, v ∈ placesOver D.host.E (D.host.g k) → v ∉ placesOver D.host.E (D.ntw.l i) →
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ ^ (D.host.g k - 1) = 1


variable {art' : Ideles D.host.E →* Gab D.host.E D.nd.Om} (K : ∀ i, Chars D C art' i) [IsEmpty D.nd.Loc]


end Record

end GlobalTheory.Triple.Model

end
