module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOne_of :
    TestOne := by
  intro p _ G
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.LKMid.isTest_indicator _ _ (by
      rintro _ ⟨k, hk, rfl⟩
      rw [GlobalTheory.LKCx.sigG_one]
      exact hk)
  · exact GlobalTheory.LKDef.HeckeTraceExample.indicator_bi _
