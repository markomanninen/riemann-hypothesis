module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ResMap

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_map :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ') [H.Normal],
      IsOpen (H : Set Γ') → Continuous f → Function.Surjective f →
        (PL (l := l) (H.comap f)).map f = PL (l := l) H := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H _ _ hf hsurj
  have hmem {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {x : G} :
      x ∈ PL (l := l) K ↔
        ∀ U : OpenNormalSubgroup G, (∀ h ∈ K, ∃ e : ℕ, h ^ l ^ e ∈ U) → x ∈ U := by
    simp only [PL, Subgroup.mem_iInf]
    rfl
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine hmem.mpr fun V hV => ?_
    let U : OpenNormalSubgroup Γ :=
      { toOpenSubgroup := V.toOpenSubgroup.comap f hf
        isNormal' := Subgroup.Normal.comap V.isNormal' f }
    apply hmem.mp hx U
    intro h hh
    obtain ⟨e, he⟩ := hV (f h) hh
    refine ⟨e, ?_⟩
    change f (h ^ l ^ e) ∈ V
    rwa [map_pow]
  · intro y hy
    let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ U}
    let top : OpenNormalSubgroup Γ :=
      { toOpenSubgroup := ⊤
        isNormal' := Subgroup.normal_top }
    have htop : ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ top := by
      intro h _
      exact ⟨0, Subgroup.mem_top _⟩
    have : Nonempty ι := ⟨⟨top, htop⟩⟩
    let t (i : ι) : Set Γ := f ⁻¹' {y} ∩ (i.1 : Set Γ)
    have hclosed (i : ι) : IsClosed (t i) :=
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (· ⊇ ·) t := by
      intro i j
      have hpow : ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ i.1 ⊓ j.1 := by
        intro h hh
        obtain ⟨a, ha⟩ := i.2 h hh
        obtain ⟨b, hb⟩ := j.2 h hh
        refine ⟨a + b, ⟨?_, ?_⟩⟩
        · rw [pow_add, pow_mul]
          exact pow_mem ha _
        · rw [add_comm, pow_add, pow_mul]
          exact pow_mem hb _
      exact ⟨⟨i.1 ⊓ j.1, hpow⟩, fun _ hx => ⟨hx.1, hx.2.1⟩, fun _ hx => ⟨hx.1, hx.2.2⟩⟩
    have hnonempty (i : ι) : (t i).Nonempty := by
      let V : OpenNormalSubgroup Γ' :=
        { toSubgroup := i.1.toSubgroup.map f
          isOpen' := f.isOpenMap_of_sigmaCompact hsurj hf _ i.1.toOpenSubgroup.isOpen
          isNormal' := Subgroup.Normal.map i.1.isNormal' f hsurj }
      have hyV : y ∈ V := by
        refine hmem.mp hy V fun h hh => ?_
        obtain ⟨x, rfl⟩ := hsurj h
        obtain ⟨e, he⟩ := i.2 x hh
        exact ⟨e, ⟨x ^ l ^ e, he, map_pow f x _⟩⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyV
      exact ⟨x, hxy, hx⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir
      hnonempty (fun i => (hclosed i).isCompact) hclosed
    rw [Set.mem_iInter] at hx
    exact ⟨x, hmem.mpr fun U hU => (hx ⟨U, hU⟩).2, (hx ⟨top, htop⟩).1⟩
