module

public import Mathlib
public import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.GenFrameSBOfSpan
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.BasisMonomialsApply

@[expose] public section

theorem coeffNormLE_iff_spanNormLE_of_hasCompl : CutKW.KWsb := GenFrameSpan.genFrameSB_of_span GenFrameSpan.stepSpan
