module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrimeStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.TypePrimes.psiG_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → TC.Pins B X → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (G : GLoc (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g), TC.IdG I l Z G → ∀ ψ, Formalism.L2.Theta.IsStdChar (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ψ (-1) → ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F), Formalism.L2.Theta.IsPlaceIdem (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) v ε → ∀ c y : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, Valued.v (algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) - G.phi k v h (inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0)) < 1 → ∀ z : v.adicCompletionIntegers (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, (z : v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) = algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) → G.psi0 k v h (IsLocalRing.residue _ z) = ψ (ε * algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) * (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) / ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))) :=
  by
    intro B X I hI _ l Z G hG ψ hψ k v h ε hε c y hc z hz
    have hs := (TC.rec7 I l Z).nd.g_split k
    have hgp := l.pr.g_prime k
    obtain ⟨hN, hsq⟩ := GlobalTheory.Mem.TypePrimes.Red.absNorm_and_unram hgp hs v h
    obtain ⟨t, ht⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer B.host
    obtain ⟨b, hb, e⟩ := GlobalTheory.Mem.TypePrimes.Red.columnCharacter_reduction_eq_exp
      (X := B.fields) (Pr := B.primes X) I.Ch l.pr B.sp.cm B.embLL B.host.xi0 hI.weil t ht G hG.piG
      (fun _ => rfl) hG.psi k v h hN c y hc z hz
    refine e.trans ?_
    exact (GlobalTheory.T.standardAddChar_placeIdempotent_div_prime (TC.rec7 I l Z) ψ hψ _
      hgp v hN hsq ε hε (c * y) (b : ℤ) (by rw [Int.cast_natCast]; exact hb)).symm
