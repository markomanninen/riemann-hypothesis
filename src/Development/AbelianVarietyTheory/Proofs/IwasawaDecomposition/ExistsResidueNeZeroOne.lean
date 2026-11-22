module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
namespace GlobalTheory.ResThree

theorem two_ne_zero_one (g : ℕ) (hg : 3 ≤ g) : (2 : ZMod g) ≠ 0 ∧ (2 : ZMod g) ≠ 1 := by
  constructor
  · intro h
    have h' : ((2 : ℕ) : ZMod g) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · intro h
    have h' : ((2 : ℕ) : ZMod g) = ((1 : ℕ) : ZMod g) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    omega

end GlobalTheory.ResThree
