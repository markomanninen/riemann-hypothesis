module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilySurjectiveIffGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFamily_surjective_iff_geometricPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  first | (exact @GlobalTheory.HTSympCover.onto_tors_iff) | (exact GlobalTheory.HTSympCover.onto_tors_iff) | (intros; apply GlobalTheory.HTSympCover.onto_tors_iff  <;> assumption)
