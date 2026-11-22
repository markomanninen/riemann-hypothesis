module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowReadingsSameRowsIdentifyDefiniteFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsSameGeometricHalf
public import Lean

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000

theorem tupTied_ext {D : D7} {cf : CharFrame D} {C : NChoice D} {p q : TupTied D cf C} (h1 : p.xi = q.xi) (h2 : p.psi = q.psi) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl

section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}

theorem nchT_up (n : NchT w Z Wt nch) : Nonempty (NchT w (upL Z S' N h) Wt (nchUp S' N h nch)) :=
  ⟨{ tp := {
       xi := by with_unfolding_all exact (n.tp.xi :)
       xi_inj := by with_unfolding_all exact (n.tp.xi_inj :)
       xi_fin := by with_unfolding_all exact (n.tp.xi_fin :)
       xi_triv := by with_unfolding_all exact (n.tp.xi_triv :)
       xi_tame := by with_unfolding_all exact (n.tp.xi_tame :)
       psi := by with_unfolding_all exact (n.tp.psi :)
       trueColumnChoices_heckeChar_reference_eq_one := by with_unfolding_all exact (n.tp.trueColumnChoices_heckeChar_reference_eq_one :)
       xi_star := by with_unfolding_all exact (n.tp.xi_star :)
       xi_star' := by with_unfolding_all exact (n.tp.xi_star' :)
       xi_tw := by with_unfolding_all exact (n.tp.xi_tw :)
       psi_is := by with_unfolding_all exact (n.tp.psi_is :)
       psi_un := by with_unfolding_all exact (n.tp.psi_un :) }
     xi := by with_unfolding_all exact (n.xi :)
     psi := by with_unfolding_all exact (n.psi :)
     tie := {
       twOf_eq := by with_unfolding_all exact (n.tie.twOf_eq :)
       twSide_eq := by with_unfolding_all exact (n.tie.twSide_eq :)
       Q_eq := by with_unfolding_all exact (n.tie.Q_eq :)
       psi_eq := by with_unfolding_all exact (n.tie.psi_eq :)
       embedding_baseField_condition := by with_unfolding_all exact (n.tie.embedding_baseField_condition :) }
     Q := n.Q
     chrPsi := by with_unfolding_all exact (n.chrPsi :) }⟩

theorem kept_up (nch : NChoice (w.D Z)) : Kept nch (nchUp S' N h nch) := by
  refine ⟨?_, ?_, ?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩ <;> constructor <;> first | rfl | exact HEq.rfl

theorem goodO_up (g : GoodO (w.D Z) nch xd) : GoodO (w.D (upL Z S' N h)) (nchUp S' N h nch) (xdUp S' N h xd) := by
  obtain ⟨⟨E, N0, S⟩, h1, h2, h3⟩ := g.tw
  cases h1
  exact ⟨⟨⟨twEOf (xdUp S' N h xd), N0, S⟩, rfl, (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :))⟩, g.sep⟩
end

end GlobalTheory.LayerMove
end
