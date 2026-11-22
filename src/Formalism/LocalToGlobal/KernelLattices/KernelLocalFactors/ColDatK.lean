module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.GlobTied
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.ChainOneP
public import Formalism.LocalToGlobal.Columns.RefXi1Above
public import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section Bridge

variable (D : D7)

variable {D}

def KapChoice.toCar {γ₀ : IsoK D} (k : KapChoice γ₀) : Cd.KapChoice (D := Car.ofRec D) γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def Base.toCar (B : Base D cc δ) : Cd.Base (Car.ofRec D) cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := B.kc.toCar

variable {X : Fields}

def Seam.toCar (s : Seam D X) : Cd.Seam (Car.ofRec D) X := ⟨s.iE, s.iT, s.σ₀⟩

end Bridge

section OverColDat

variable (d : ColDat)

variable {d}


end OverColDat

namespace Test

open Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits

end Test

end Formalism.L2.Ker
