module

public import Formalism.SmithDeterminants.StatementGram

@[expose] public section

open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E

def fock {R τ : Type*} [CommRing R] [StarRing R] (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)

end Formalism.E
