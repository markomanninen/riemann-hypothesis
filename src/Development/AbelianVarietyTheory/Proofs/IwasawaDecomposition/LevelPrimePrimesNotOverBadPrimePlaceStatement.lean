module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimePrimesNotOverBadPrimePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Formalism.LocalToGlobal.Columns.DecoFin

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_primes_not_over_bad_prime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof | exact GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof | (intros; apply GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof <;> assumption)
