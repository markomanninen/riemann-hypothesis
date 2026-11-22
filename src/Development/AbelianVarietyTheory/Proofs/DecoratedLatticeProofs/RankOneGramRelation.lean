module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
public import Formalism.LocalRingCardinality.PosOfIsomEmb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsCharactersFamily

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamChars

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

variable {D : D7}

theorem cu_mul {χ χ' : (AE D)ˣ →* Circle} {x : HeightOneSpectrum (𝓞 D.host.F)} (h : CharUnramAt D χ x)
    (h' : CharUnramAt D χ' x) : CharUnramAt D (χ * χ') x := fun y h1 h2 h3 h4 => by
  rw [MonoidHom.mul_apply, h y h1 h2 h3 h4, h' y h1 h2 h3 h4, one_mul]

theorem cu_inv {χ : (AE D)ˣ →* Circle} {x : HeightOneSpectrum (𝓞 D.host.F)} (h : CharUnramAt D χ x) :
    CharUnramAt D χ⁻¹ x := fun y h1 h2 h3 h4 => by
  rw [MonoidHom.inv_apply, h y h1 h2 h3 h4, inv_one]

theorem mem_under (PP : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) :
    ((n : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal ↔ ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((n : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem not_both (PP : HeightOneSpectrum (𝓞 D.host.E)) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hb : ((b : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  haveI : PP.asIdeal.IsPrime := PP.isPrime
  have ha' : ((a : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 ha
  have hb' : ((b : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hb
  exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_coprimes hab (ringChar.dvd ha') (ringChar.dvd hb'))

end GlobalTheory.FamChars

namespace GlobalTheory.FamChars

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

theorem weil_rec {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

end GlobalTheory.FamChars
