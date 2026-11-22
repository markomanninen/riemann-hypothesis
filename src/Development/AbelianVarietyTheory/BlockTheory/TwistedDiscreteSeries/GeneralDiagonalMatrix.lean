module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattice

variable {D : D7}

def StabLat (V : HSp D) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def LevAgrees (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (κ : GA D V)
    (lev : La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
    finVec V (ι (lev a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w

end Lattice

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Frames

section Statement

variable {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)


include hT hj hσ in
theorem dict_mem_dom (h : GA D (T.V j σ)) : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom := by
  obtain ⟨_, _, _, hd⟩ := hT.dictU j hj σ hσ
  exact hd.2.2.2.1 h


end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix
