module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTuple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_twistPlace_referenceTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  intro B X I _ v ⟨P, hP, _⟩
  have hEmpty : P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) :=
    I.twistPrimes_reference_tuple_eq_empty ▸ hP
  simp at hEmpty
