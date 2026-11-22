module

public import Mathlib
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.DataParams

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Exceptional

variable {D : D7} (L : SizeData₂ D)

end Exceptional

section Terms

variable (D : D7) (i : D.nd.Loc)

def ramLen : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)})

def ccLen (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)

def selLen (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i (fun _ => ρ) π)

def shaSum : ℕ∞ :=
  ∑ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

def zetaP (P : HeightOneSpectrum (𝓞 D.host.E)) : D.nd.O i :=
  ((D.ntw.psiL i (D.nd.gam0 i P) : (D.nd.O i)ˣ) : D.nd.O i)

def twistLen : ℕ∞ :=
  (D.R.t : ℕ∞) * ∑ P ∈ D.nd.Q i,
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {zetaP D i P - 1})

end Terms

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

end
