module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.IwJac

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

variable {k n}

def tor (ϖ : kˣ) (x : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => ϖ ^ x i

end GlobalTheory.CompanionTheory.IwJac

end
