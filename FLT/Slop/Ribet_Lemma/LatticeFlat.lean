/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Slop.Ribet_Lemma.LatticeGaloisRep
public import FLT.GroupScheme.FiniteFlatSubobject

/-!
# Flatness of commensurate stable lattices

Finite-flat Galois modules are closed under subquotients. Applying this to
sufficiently deep reductions transfers flatness between stable lattices.
-/

@[expose] public section

open scoped TensorProduct Pointwise NumberField

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan

/-- An equivariant quotient of an equivariant image in a finite-flat module
is finite flat. The kernel inclusion expresses that the second map factors
through the image of the first. -/
theorem finiteFlat_of_subquotient
    {R F L X Y Z : Type} [CommRing R] [Field F] [Field L]
    [Algebra R F] [Algebra F L] [IsDedekindDomain R] [IsFractionRing R F]
    [IsGalois F L] [IsSepClosed L]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [DistribMulAction (L ≃ₐ[F] L) X] [DistribMulAction (L ≃ₐ[F] L) Y]
    [DistribMulAction (L ≃ₐ[F] L) Z]
    (hX : GaloisModule.IsFiniteFlat R F L X)
    (f : Y →+[L ≃ₐ[F] L] X) (q : Y →+[L ≃ₐ[F] L] Z)
    (hq : Function.Surjective q)
    (hker : f.toAddMonoidHom.ker ≤ q.toAddMonoidHom.ker) :
    GaloisModule.IsFiniteFlat R F L Z := by
  let S := f.toAddMonoidHom.range
  let _ : SMul (L ≃ₐ[F] L) S := ⟨fun g x ↦
    ⟨g • x.val, by
      obtain ⟨y, hy⟩ := x.property
      exact ⟨g • y, (map_smul f g y).trans (congrArg (g • ·) hy)⟩⟩⟩
  let _ : DistribMulAction (L ≃ₐ[F] L) S :=
    Function.Injective.distribMulAction S.subtype Subtype.val_injective (fun _ _ ↦ rfl)
  let i : S →+[L ≃ₐ[F] L] X :=
    { S.subtype with map_smul' := fun _ _ ↦ rfl }
  have hS := hX.subobject R F L X i Subtype.val_injective
  let f' : Y →+ S := f.toAddMonoidHom.rangeRestrict
  have hf' : Function.Surjective f' := f.toAddMonoidHom.rangeRestrict_surjective
  have hk : f'.ker ≤ q.toAddMonoidHom.ker := by
    intro y hy
    apply hker
    exact congrArg Subtype.val hy
  let q' : S →+ Z := f'.liftOfSurjective hf' ⟨q.toAddMonoidHom, hk⟩
  have hq' (y : Y) : q' (f' y) = q y := by simp [q']
  let t : S →+[L ≃ₐ[F] L] Z :=
    { q' with
      map_smul' := by
        intro g x
        obtain ⟨y, rfl⟩ := hf' x
        have he : g • f' y = f' (g • y) := Subtype.ext (map_smul f g y).symm
        change q' (g • f' y) = g • q' (f' y)
        rw [he, hq', hq', map_smul] }
  apply hS.quotient R F L S t
  intro z
  obtain ⟨y, rfl⟩ := hq z
  exact ⟨f' y, hq' y⟩

section Coefficients

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K]

omit [IsTopologicalRing O] in
/-- Powers of an open principal ideal remain open when the coefficient
ring has the topology induced from its fraction field. -/
theorem isOpen_span_pow (hOK : Topology.IsInducing (algebraMap O K))
    (j : O) (hj : IsOpen (Ideal.span {j} : Set O)) (n : ℕ) :
    IsOpen (Ideal.span {j ^ n} : Set O) := by
  by_cases hj0 : j = 0
  · subst j
    cases n with
    | zero => simp
    | succ n => simpa using hj
  have hjK : algebraMap O K j ≠ 0 := by
    exact fun h ↦ hj0 (IsFractionRing.injective O K (by simpa using h))
  have hi : Topology.IsInducing (fun x : O ↦ j * x) := by
    apply hOK.of_comp_iff.mp
    convert (Homeomorph.smulOfNeZero (algebraMap O K j) hjK).isInducing.comp hOK using 1
    ext x
    simp
  have ho : IsOpenMap (fun x : O ↦ j * x) := by
    apply hi.isOpenMap
    convert hj using 1
    ext x
    simp only [Set.mem_range, SetLike.mem_coe, Ideal.mem_span_singleton, dvd_def, eq_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    convert ho _ ih using 1
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨j ^ n * z, ⟨z, rfl⟩, by ring⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, by ring⟩

omit [TopologicalSpace O] [IsTopologicalRing O] in
/-- Powers of a proper ideal in a DVR eventually lie in any prescribed
nonzero principal ideal. -/
theorem exists_dvd_pow_of_not_isUnit (j c : O) (hj : ¬ IsUnit j) (hc : c ≠ 0) :
    ∃ n : ℕ, c ∣ j ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {c}) (by simpa using hc) hπ
  refine ⟨n, ?_⟩
  have hjπ : j ∈ Ideal.span {π} := by
    rw [← hπ.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal]
    exact hj
  have hpow : j ^ n ∈ Ideal.span {π ^ n} :=
    Ideal.mem_span_singleton.mpr (pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.mp hjπ) n)
  rw [← hn] at hpow
  exact Ideal.mem_span_singleton.mp hpow

/-- The quotient tensor map has exactly the expected ideal multiple as kernel. -/
theorem one_tmul_eq_zero_iff {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) (x : M) :
    (1 : A ⧸ I) ⊗ₜ[A] x = 0 ↔ x ∈ (I • ⊤ : Submodule A M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

/-- Every tensor over a quotient coefficient ring comes from an integral vector. -/
theorem one_tmul_surjective {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) :
    Function.Surjective (fun x : M ↦ (1 : A ⧸ I) ⊗ₜ[A] x) := by
  intro y
  obtain ⟨x, hx⟩ := (I • ⊤ : Submodule A M).mkQ_surjective
    (TensorProduct.quotTensorEquivQuotSMul M I y)
  refine ⟨x, (TensorProduct.quotTensorEquivQuotSMul M I).injective ?_⟩
  simpa using hx

end Coefficients

/-- Finite-flatness at every open coefficient ideal is independent of the
stable lattice. The place is arbitrary, in particular it may be the place at three. -/
theorem flat_three_of_stable_lattice
    {O K W : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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
  apply finiteFlat_of_subquotient (hflat.cond I hiopen) f₀ q (one_tmul_surjective (M := Λ) J)
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
