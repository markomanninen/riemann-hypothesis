module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FubiniStudyChowHeight

@[expose] public section

namespace GlobalTheory.CovTop

structure HypothesesX : Prop where

  ks : GlobalTheory.Published.ToroidalForFanKS

  lie : GlobalTheory.Published.SemiAbelianLieSeminegative

  green : GlobalTheory.Published.GreenCuspidal

  sep : GlobalTheory.Published.PointSeparationPair

  fsch : GlobalTheory.Published.FubiniStudyChowHeight

end GlobalTheory.CovTop
