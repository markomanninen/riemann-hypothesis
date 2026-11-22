module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb.G3

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem map_frob_w (r : Res l K) (w : WittVector l r.k) :
    WittVector.map r.s (WittVector.frobenius w) = WittVector.frobenius (WittVector.map r.s w) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [WittVector.map_coeff, frobenius_def, map_pow]

theorem w_phi (r : Res l K) (w : WittVector l r.k) :
    ACris.phi (K := ℂ_[l]) (p := l) (r.w w) = r.w (WittVector.frobenius w) := by
  show ACris.phi (K := ℂ_[l]) (p := l)
    (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w)) =
    algebraMap (Ainf l) (Acris l) (WittVector.map r.s (WittVector.frobenius w))
  rw [ACris.phi_algebraMap, map_frob_w]
  rfl

end CrystallineSemistableComparison.Pb.G3
