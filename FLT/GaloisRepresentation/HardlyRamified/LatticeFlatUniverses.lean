/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Slop.Ribet_Lemma.LatticeFlat
public import FLT.GaloisRepresentation.HardlyRamified.SubquotientUniverses

/-! # Flatness of commensurate lattices in arbitrary universes -/

@[expose] public noncomputable section
open scoped TensorProduct Pointwise NumberField
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan

/-- Finite-flatness at every open coefficient ideal is independent of the
stable lattice. The place is arbitrary, in particular it may be the place at three. -/
theorem flat_of_stable_lattice_universes
    {O K W : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
    [TopologicalSpace O] [IsTopologicalRing O]
    [TopologicalSpace K] [IsTopologicalRing K]
    (ρK : GaloisRep ℚ K W) (Λ₀ Λ : Submodule O W)
    (h₀ : StableLattice.IsStableLattice ρK.toRepresentation Λ₀)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hflat : letI := h₀.isLattice
      (latticeGaloisRep ρK Λ₀ h₀ hOK).IsFlatAt v) :
    letI := hΛ.isLattice
    (latticeGaloisRep ρK Λ hΛ hOK).IsFlatAt v := by
  classical
  let _ := h₀.isLattice
  let _ := hΛ.isLattice
  obtain ⟨a, ha, haΛ⟩ := Submodule.IsLattice.exists_smul_le Λ₀ Λ
  obtain ⟨b, hb, hbΛ⟩ := Submodule.IsLattice.exists_smul_le Λ Λ₀
  let f : Λ →ₗ[O] Λ₀ :=
    { toFun := fun x ↦ ⟨a • x.val, haΛ (Submodule.smul_mem_pointwise_smul _ _ _ x.property)⟩
      map_add' := fun x y ↦ Subtype.ext (smul_add a x.val y.val)
      map_smul' := fun r x ↦ Subtype.ext (smul_comm a r x.val) }
  constructor
  intro J hJ
  let j := Submodule.IsPrincipal.generator J
  have hj : Ideal.span {j} = J := Ideal.span_singleton_generator J
  obtain ⟨i, hiopen, hi⟩ : ∃ i : O, IsOpen (Ideal.span {i} : Set O) ∧
      (IsUnit j ∨ a * b * j ∣ i) := by
    by_cases hju : IsUnit j
    · exact ⟨1, by simp, Or.inl hju⟩
    obtain ⟨n, d, hd⟩ := exists_dvd_pow_of_not_isUnit j (a * b) hju (mul_ne_zero ha hb)
    refine ⟨j ^ (n + 1), isOpen_span_pow hOK j (by rwa [hj]) _, Or.inr ⟨d, ?_⟩⟩
    rw [pow_succ, hd]
    ring
  let I : Ideal O := Ideal.span {i}
  let σ₀ := ((latticeGaloisRep ρK Λ₀ h₀ hOK).baseChange (O ⧸ I)).toLocal v
  let σ := ((latticeGaloisRep ρK Λ hΛ hOK).baseChange (O ⧸ J)).toLocal v
  let τ := (latticeGaloisRep ρK Λ hΛ hOK).toLocal v
  let _ : Module O τ.Space := inferInstanceAs (Module O Λ)
  let f₀ : τ.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] σ₀.Space :=
    { toFun := fun x ↦ (1 : O ⧸ I) ⊗ₜ[O] f x
      map_zero' := by simp
      map_add' := by
        intro x y
        change (1 : O ⧸ I) ⊗ₜ[O] f ((x : Λ) + (y : Λ)) = _
        rw [map_add, TensorProduct.tmul_add]
      map_smul' := by
        intro g x
        change (1 : O ⧸ I) ⊗ₜ[O] f (τ g x) =
          (1 : O ⧸ I) ⊗ₜ[O] ((latticeGaloisRep ρK Λ₀ h₀ hOK).toLocal v g (f x))
        congr 1
        apply Subtype.ext
        exact (ρK _).map_smul_of_tower a (x : Λ).val |>.symm }
  let q : τ.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] σ.Space :=
    { toFun := fun x ↦ (1 : O ⧸ J) ⊗ₜ[O] x
      map_zero' := by simp
      map_add' := fun x y ↦ TensorProduct.tmul_add _ (x : Λ) (y : Λ)
      map_smul' := fun _ _ ↦ rfl }
  apply finiteFlat_of_subquotient_universes (hflat.cond I hiopen) f₀ q
    (one_tmul_surjective (M := Λ) J)
  intro x hx
  change (1 : O ⧸ J) ⊗ₜ[O] (x : Λ) = 0
  rw [one_tmul_eq_zero_iff, ← hj, Submodule.ideal_span_singleton_smul]
  rcases hi with hju | ⟨d, hd⟩
  · rw [← Submodule.ideal_span_singleton_smul, Ideal.span_singleton_eq_top.mpr hju]
    simp
  change (1 : O ⧸ I) ⊗ₜ[O] f x = 0 at hx
  rw [one_tmul_eq_zero_iff, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨y, _, hy⟩ := hx
  let z : Λ := ⟨b • (d • y.val), hbΛ
    (Submodule.smul_mem_pointwise_smul _ _ _ (Λ₀.smul_mem d y.property))⟩
  have hax : a • (x : Λ).val = a • (j • z.val) := by
    have h := congrArg Subtype.val hy
    change i • y.val = a • (x : Λ).val at h
    rw [← h, hd]
    simp only [z, mul_smul]
    simp only [smul_comm b j]
  have haK : algebraMap O K a ≠ 0 := by
    exact fun h ↦ ha (IsFractionRing.injective O K (by simpa using h))
  have hxz : (x : Λ) = j • z := by
    apply Subtype.ext
    change (x : Λ).val = j • z.val
    have h := congrArg (fun w : W ↦ (algebraMap O K a)⁻¹ • w) hax
    simpa only [← algebraMap_smul K a, inv_smul_smul₀ haK] using h
  rw [Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨z, Submodule.mem_top, hxz.symm⟩


end ThreeAdicPlan
