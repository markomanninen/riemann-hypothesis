module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def dimQ (b : Bool) : ℕ := (lv (F.fc (R.toCx F).zs) b).dQ A.μ0

theorem dimQ_eq (b : Bool) :
    dimQ R F b = Module.finrank D.what₂.LL ((A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0)) := by
  cases b <;> rfl

theorem pos_iff (b : Bool) : (lv (F.fc (R.toCx F).zs) b).Pos ↔ 0 < dimQ R F b := Iff.rfl

theorem pos_iff_ne_bot (b : Bool) :
    (lv (F.fc (R.toCx F).zs) b).Pos ↔ (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ := by
  rw [pos_iff, dimQ_eq, pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]

end

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

end
