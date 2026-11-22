module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransportOfLatClaims
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertClassFieldLatticeTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodExistenceCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionOfFunctionalEquation

@[expose] public section

theorem GlobalTheory.JoinFun.joinOut_of_lat : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatVal.LatIntRam → GlobalTheory.LatVal.LatIntUnr → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  intro hEM hHCF hSKDR hHT hRam hUnr hLatAlg hLatConj
  have hZD := GlobalTheory.ZetaDenom.zetaDenominators hSKDR
  have hField := GlobalTheory.SqTop.fieldDat
  have hAbs := GlobalTheory.Published.HeckeTateFunctionalEquation.abs hHT
  have hLNe := GlobalTheory.SqTop.lNe_of_functionalEquation hAbs GlobalTheory.HeckeStrip.completedLBoundedInStrips hField
  exact ⟨GlobalTheory.ToricDenomRow.toricDenominator hZD hRam hUnr,
    GlobalTheory.TransportProof.transport_of hHCF hLatAlg hLatConj,
    GlobalTheory.TwistedTransportProof.main (GlobalTheory.LatVal.periodEx_of_mainTheorem hEM) hLatAlg hLatConj, hZD,
    GlobalTheory.SqTop.refl_of_functionalEquation hHT hField hLNe⟩
