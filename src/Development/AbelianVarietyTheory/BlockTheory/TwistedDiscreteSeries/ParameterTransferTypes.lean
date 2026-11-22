module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Satake

def SpanAt (V : HSp D) (e : AE D) (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (γ : GA D V) : Prop :=
  (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, IntVec z ∧
    (fun a => finPart D e * (finMat D.sp.cm.sig V.gram γ).mulVec y a) = fun a => finPart D e * M.mulVec z a) ∧
  (∀ z, IntVec z → ∃ y ∈ Formalism.L2.NTheta.LamHat V,
    (fun a => finPart D e * (finMat D.sp.cm.sig V.gram γ).mulVec y a) = fun a => finPart D e * M.mulVec z a)


open Classical in
def sphVal {n : ℕ} (inert : Prop) (q : ℕ) (α : Fin n → ℂ) (a : Fin n → ℤ) : ℂ :=
  ∏ i : Fin n, if inert → 2 * (i : ℕ) + 1 < n then
    (α i * (((q : ℝ) ^ (-(((n : ℝ) - 1 - 2 * (i : ℕ)) / 2)) : ℝ) : ℂ)) ^ a i else 1

def str (x : ℂ) (q t : ℕ) : Multiset ℂ :=
  (Multiset.range t).map fun k => x * (((q : ℝ) ^ (((t : ℝ) - 1) / 2 - (k : ℝ)) : ℝ) : ℂ)

end Satake

section Spaces

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : _root_.Formalism.IndefR.Links.RealDat D A Ks) (F : Face D A)


open Classical in
def badS (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

end Spaces

end GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

end
