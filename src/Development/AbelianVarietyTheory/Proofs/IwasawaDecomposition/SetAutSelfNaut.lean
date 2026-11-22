module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

@[expose] public section

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

def RowWD.unram (D : D7) (m : D.what₂.FT → PlE D.host → Multiset ℂ) (h0 : ∀ σ w, (0:ℂ) ∉ m σ w)
    (hc : ∀ σ w, Multiset.card (m σ w) = D.R.r) : RowWD D where
  par σ w := WD.lpUnr (D.nd.plOm.2 w) (m σ w)
  sat := m
  dim σ w := (WD.lpUnr_spec (h := D.nd.plOm.2 w) (m σ w) (h0 σ w)).2.2.trans (hc σ w)
  tame σ k v :=
    let w := D.naut.plGw k v
    WD.tame_of_unr (WD.lpUnr_spec (h := D.nd.plOm.2 w) (m σ w) (h0 σ w)).1

end GlobalTheory.HeightCounting
end
