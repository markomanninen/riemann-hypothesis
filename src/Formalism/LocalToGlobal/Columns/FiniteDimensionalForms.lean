module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.ToHLat
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas

@[expose] public section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

abbrev outSec : ∀ b, (F.mem b).Sec := fun b => (F.mem b).outSec

abbrev rep (c : F.Cl) : F.D c.1 := (F.mem c.1).outSec.rep c.2

def res (h : F.Ok) : F.Forms ≃ₗ[K] (F.toCSD h).Forms := F.resOf h F.outSec

def gramV : Matrix F.ιV F.ιV K := Matrix.of fun i j => F.pair (F.bV i) (F.bV j)

structure Rat : Prop where
  pair_rat : ∀ i j, F.gramV i j ∈ cmMax K
  act_rat : ∀ (b : F.β) (g : F.G b) i j, F.bV.repr (F.ρ b g (F.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef

def Free : Prop := ∀ b, (F.mem b).Free

@[reducible] def toH (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : HLat K where
  V := F.Forms
  ι := Fin (F.toCSD h).dim
  b := (F.toCSD h).basis.map (F.res h).symm
  X := stdFrame (F.toCSD h).H
  L := L



variable {F}

variable (F)

variable {F}

variable (F)

variable {F}

end GFam

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

def intOf (N : ∀ b, F.D b → Submodule (𝓞 K) F.V) : Submodule (𝓞 K) F.Forms :=
  Submodule.pi Set.univ fun b => (F.mem b).intOf (N b)

end GFam

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end GSD

section FormFam

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} {β : Type} [Fintype β] [DecidableEq β]


variable (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : β → LevFam X.E X.K n SG)

end FormFam

end Formalism.L2.Col
