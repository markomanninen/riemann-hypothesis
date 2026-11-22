module

public import Development.EtaleCohomology.WeilConjectures.FermatCount
public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
public import Development.EtaleCohomology.KummerTheory.InjSlice

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EWeil.AcycPf

def incl (S : Scheme.{0}) : S.Etale ⥤ Over S := MorphismProperty.Over.forget _ _ _

def RestrInj : Prop := ∀ (R : Type) [CommRing R] (S : Scheme.{0})
  (G : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))) [Injective G],
  ∃ h : Presheaf.IsSheaf S.smallEtaleTopology ((incl S).op ⋙ G.obj),
    Injective (⟨_, h⟩ : Sheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R)))

end LateralTheory.EWeil.AcycPf
