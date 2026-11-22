module

public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Formalism.LocalToGlobal.HermitianForms.Transport
public import Formalism.LocalToGlobal.HermitianForms.FramesLemmas

@[expose] public section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m}




set_option maxHeartbeats 4000000 in
theorem UpNatTie.upTie {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : UpNatTie P K W) :
    UpTie P K W := by
  intro v c z hz
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h v c z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g hg => ?_⟩
  funext s
  obtain ⟨y', hy'⟩ := exists_isTr' (embT D) γ.1 (W.eY s)
  have hs : IsTr (atInf (embT D) γ.1.1) (W.eY (W.eY.symm y')) (W.eY s) := by
    rw [Equiv.apply_symm_apply]; exact hy'
  rw [h6 _ s _ hs]
  exact (AdFun_transport K.lev (embT D) g hg γ.1 γ.2 (K.y c * η) _ κ h2 _ _ hs).symm


end Formalism.L2.Forms
