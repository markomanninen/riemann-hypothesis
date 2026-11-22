module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section OfTower

variable (W : GlobalTheory.Core.Rk.Tower D)

def comOf : Com D := ⟨W.θ, W.ψ, W.toLevCh.mu (), W.eta, W.Pg, W.triv, W.chi⟩

def stageY (j : ℕ) : PiLocalization₂ D :=
  ⟨Yc D j, parB (Ptw D) (min j D.R.m), W.MY j, W.ΛY j, W.βY j, W.datYt () j W.triv, W.νY j, W.fdY j⟩

def stageX : PiLocalization₂ D := ⟨D.sp.X', parB (Ptw D) D.R.m, W.MX, W.ΛX, W.βX, W.datXt (), W.νX, W.fdX⟩

def stepY (k : ℕ) : Step (comOf W) (stageY W k) (stageY W (k + 1)) := ⟨W.ωY k, W.vY k, W.ItY k, W.ioY k⟩

def stepX : Step (comOf W) (stageY W (D.R.m - 1)) (stageX W) := ⟨W.ωX, W.vX, W.ItX, W.ioX⟩

end OfTower

def PiLocalization₂.InFlag (s : PiLocalization₂ D) (κ : GA D s.V) : Prop :=
  κ ∈ GfC s.V ∧ Lev.finE s.V κ ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β s.L

def SameBlock (s s' : PiLocalization₂ D) (κ : GA D s.V) (κ' : GA D s'.V) : Prop :=
  HEq (Formalism.L2.DIV.rTup s.β s.L (Lev.finE s.V κ)) (Formalism.L2.DIV.rTup s'.β s'.L (Lev.finE s'.V κ'))

end GlobalTheory.ChainOnto

end
