module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignFlatDictionaryAtOnePlaceLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryRelativeBaseVacuaLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductDependsOnDataProductStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem exists_locAt_big : Big fun ch => ∃ s, LocAt ch s :=
  GlobalTheory.RowReal.big_mono (fun ch h => by
               obtain ⟨⟨⟨s, hP⟩, hC⟩, hL⟩ := h
               exact ⟨s, hL s hP hC⟩)
    (Big.and (Big.and GlobalTheory.T.exists_sign_flatDictionaryAtOnePlace_largeDepth GlobalTheory.T.unfoldedProduct_depends_on_dataProduct) GlobalTheory.T.flat_dictionary_relative_base_vacua_large_depth)

end GlobalTheory.RowVal
