module

public import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifGen

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

section Per

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


open Classical in
def bdet (X : Data E r) (b : Frame X.Ψ r) : ℂ :=
  ∏ τ : X.Ψ, ∏ j : Fin r, b τ j j ^ (if X.p0 ≤ (j : ℕ) then (1 : ℤ) else -1)

end Per

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
  (M : ModelsOf F r)

abbrev PerAt : Prop :=
  ∀ k, ∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (pmOf e M k x)

def lieOf (hP : PerAt e F M) (k : Fin F.n) (x : (M.X k).dom) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left :=
  (derivAt_exists (hP k x.1 x.2) (eb e τ i)).choose

def LieEig : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ τ (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), IsTanAt (S := CAt σ) (F.u i P) v → IsEigAt c τ v →
      ∃ a : Fin (Dw.mult τ) → ℂ, IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, a j • eb e τ j) v

abbrev GenSec : Type :=
  ∀ k (x : (M.X k).dom), LB.Sec (PPx (S := CAt σ) (F.u k (pmOf e M k x.1)))

abbrev IsGenSec (s : GenSec e F M) : Prop :=
  ∀ k (x : (M.X k).dom) (s' : LB.Sec (PPx (S := CAt σ) (F.u k (pmOf e M k x.1)))),
    ∃! a : CAt σ, ∀ i, s'.f i = scal (S := CAt σ) (F.u k (pmOf e M k x.1)) a i * (s k x).f i


end Fam

section Red

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}
  (hTE : ExpTan e F) (hEL : ExpLin e F) (hLE : LieEig e F) (hP : PerAt e F M) (s : GenSec e F M)
  (hs : IsGenSec e F M s)

end Red

section Row

variable {D : D7}

end Row

section Gam

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem det_map_ne (τ : E →+* ℂ) (γ : GL (Fin r) E) : ((γ : Matrix (Fin r) (Fin r) E).map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).2 (Matrix.isUnits_det_units γ).ne_zero

end Gam

section GamL

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}


end GamL

end Formalism.L2.Pj
