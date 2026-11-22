module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsSecZ (G : WTZ E) (f : Rul Xo c) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
    ∀ (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R), FrBor t y y' →
      f p y' = ((∏ i, t i ^ exZ Dw G i : (p.R)ˣ) : p.R) * f p y

theorem isSecZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    IsSecZ (wtZ a n) f ↔ f ∈ sec Xo c a n := by
  have key : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      ((∏ i, t i ^ exZ Dw (wtZ a n) i : Sˣ) : S) = wchar (ex Dw a n) t := by
    intro S _ t
    rw [wchar, Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, wtZ, ex]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [← key]; exact h2 p t y y' hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [key]; exact h2 p t y y' hb⟩


variable (Xo c) in
structure Input : Type where

  D : ℕ
  N : ℕ
  T : ℕ
  i : ℕ
  g0 : ℕ

  cc : ℝ

  wL : WTZ E
  wF : WTZ E
  wde : WTZ E

  Mr : Set (Rul Xo c)

  w : Fin (N + 1) → Rul Xo c
  jc : Comp Xo c → Fin (N + 1)

  np : ℕ
  thp : Fin np → Rul Xo c

  n0 : ℕ
  th0 : Fin n0 → Rul Xo c

  nk : ℕ
  thk : Fin nk → Rul Xo c

  et : Rul Xo c
  ta1 : Rul Xo c
  ta2 : Rul Xo c

  nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ

  ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ

  wsize : WTZ E → ℝ
  DF : ℝ
  cNu : ℝ
  cQuot : ℝ
  cLow : ℝ
  cLow' : ℝ
  cDim : ℝ
  cGen : ℝ
  crystallineInclusion : ℝ
  cEta : ℝ
  cBase : ℝ
  cBase' : ℝ
  cRank : ℝ
  cField : ℝ
  f : ℝ
  r : ℝ

namespace Input

variable (I : Input Xo c)

end Input

variable (Xo c)

variable {Xo c}

section
variable [Fintype (Comp Xo c)] (I : Input Xo c) (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

end

end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
