module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationExistsEtaleOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Subsingleton A.K → WeilAt A := by
  first | exact @GlobalTheory.JR.weilAt_of_subsingleton | exact GlobalTheory.JR.weilAt_of_subsingleton | (intros; apply GlobalTheory.JR.weilAt_of_subsingleton <;> assumption)
