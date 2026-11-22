module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatDegreeStOfResKGaga
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GagaSections

@[expose] public section

theorem FlatDegreeResidue.flatDegreeSt_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.FlatCore.FlatDegreeSt :=
  fun h => GlobalTheory.CompanionTheory.Ar.Br.flatDegreeSt_of_resK_gaga h GlobalTheory.CompanionTheory.Gaga.gagaSections
