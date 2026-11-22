module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CayleyInverseConjTransposeMulApply
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZero
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumSection
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerFin
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalCharacterInvMul
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpC
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolParam
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RightConn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CompactUnitaryT2Space
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenTop

@[expose] public section

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem absThm_of (hLV : LV) (hC : Cyc) (hLC : LC) (hN : NullIff) : AbsThm := by
  have hZ := secZero hN
  have hS := sph iwa mult
  have hT := thSph_of kAK mult derivative_vacuum_section hS hZ holParam hLC hN
  have hV := vacOut_of' detU1 (locOp hLV iwa mult holParam) holParam hT
  exact absThm_of' hV iwa detU1 kAK mult hZ derivative_vacuum_section (cycSec_of hC hZ secDer) hS holParam glue hLC hN

theorem genCore_top (hC : Cyc) (hLC : LC) (hN : NullIff) : GenCore := by
  have hZ := secZero hN
  exact genCore iwa detU1 kAK mult hZ derivative_vacuum_section (cycSec_of hC hZ secDer) holParam glue hLC

end PositivityTheory.Rg.Sw.AbsSt
