module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CaraianiTempered : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 2 ≤ n →
    ∀ π : CuspSub L n, π.IsCsd → GKCoh.IsCohomological π →
      ∀ (y : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (y.adicCompletion L))), π.IsLocComp y σ →
        LocGL.IsTemperedCoeff σ.ρ

end GlobalTheory.Published
