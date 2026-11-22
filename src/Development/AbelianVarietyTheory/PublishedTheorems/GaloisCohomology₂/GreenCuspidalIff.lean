module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

open Polynomial

namespace GlobalTheory.Published

def GreenCuspidal : Prop := GlobalTheory.GLq.Green

theorem GreenCuspidal.green (h : GreenCuspidal) : GlobalTheory.GLq.Green := h

end GlobalTheory.Published
