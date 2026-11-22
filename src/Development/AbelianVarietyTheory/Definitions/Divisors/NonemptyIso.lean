module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompAlt

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.RepFamModel
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem objMap_refl {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) :
    Nonempty (ObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }⟩

variable {b : Base D R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
  {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

end GlobalTheory.UPel.HT.RepFamModel
