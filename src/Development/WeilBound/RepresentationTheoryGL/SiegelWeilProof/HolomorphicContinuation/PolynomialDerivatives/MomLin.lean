module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullSecKAlg
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PolyExpBound

@[expose] public section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

theorem momLin : MomLin := by
  intro m n c hc P Q r
  have hP := NullS.integrable_pg c hc P
  have hQ := NullS.integrable_pg c hc Q
  constructor
  · unfold mom
    rw [← integral_add hP hQ]
    congr 1
    funext x
    simp [evX]
    ring
  · unfold mom
    rw [← integral_const_mul]
    congr 1
    funext x
    simp [evX]
    ring

end PositivityTheory.Rg.Sw.LC
