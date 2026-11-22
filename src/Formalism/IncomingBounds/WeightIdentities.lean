module

public import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
public import Formalism.IncomingBounds.FlowDegreeBounds.LemmaF
public import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
public import Formalism.IncomingBounds.FlowDegreeBounds.BaseTermLeTopTerm
public import Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd
public import Mathlib
public import Formalism.IncomingBounds.LevelTail
public import Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds
public import Formalism.IncomingBounds.FlowDegreeBounds.Cayley
public import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco

@[expose] public section

namespace Formalism.IncomingBounds

theorem lemmaFa : LemmaFa := strongDuality
theorem lemmaFc : LemmaFc := lemmaFc_of maxFlowValueAttained strongDuality
theorem incomingBound : IncomingBound := incomingBound_of maxFlowValueAttained strongDuality
theorem cayleyId : CayleyId := cayleyIdentity

end Formalism.IncomingBounds
