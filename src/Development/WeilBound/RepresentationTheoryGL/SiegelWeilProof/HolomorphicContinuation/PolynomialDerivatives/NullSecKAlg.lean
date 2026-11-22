module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def MomLin : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (P Q : PX m n) (r : ℂ), mom c (P + Q) = mom c P + mom c Q ∧ mom c (r • P) = r * mom c P

end PositivityTheory.Rg.Sw.LC
