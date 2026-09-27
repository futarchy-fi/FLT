/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Mathlib.NumberTheory.NumberField.AdeleRing
public import FLT.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.OpenSubgroup
public import FLT.Mathlib.Algebra.IsQuaternionAlgebra
public import FLT.AutomorphicForm.GroupTheoryStuff
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import FLT.QuaternionAlgebra.NumberField
public import FLT.Mathlib.Topology.Instances.Matrix

/-!
# Finiteness of projective units in a totally definite quaternion algebra

Conjugation kills precisely the scalar units. At real places it preserves the
Hamilton norm, while a compact set modulo finite-adelic scalars has compact
conjugation coefficients. Discreteness of the number field in its full adeles
then makes each coefficient range finite.

The resulting `finiteRelIndex_of_compact_mod_scalars` applies to any subgroup
whose finite-adelic image is contained in a compact set times the scalar units.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField
namespace NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]

theorem isDiscrete_range_algebraMap :
    IsDiscrete (Set.range (algebraMap K (AdeleRing (𝓞 K) K))) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro _ ⟨x, rfl⟩
  obtain ⟨U, hU, hx⟩ := discrete K x
  refine ⟨U, hU, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, y, rfl⟩
    have hy : y = x := Set.mem_singleton_iff.mp (hx ▸ hz)
    simp [hy]
  · rintro rfl
    exact ⟨by have h : x ∈ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U := by
                rw [hx]; exact Set.mem_singleton x
              exact h, ⟨x, rfl⟩⟩

theorem finite_preimage_compact {S : Set (AdeleRing (𝓞 K) K)} (hS : IsCompact S) :
    Set.Finite ((algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' S) := by
  apply tendsto_cofinite_cocompact_iff.mp ?_ S hS
  have hinj : Function.Injective (algebraMap K (AdeleRing (𝓞 K) K)) := by
    intro x y hxy
    obtain ⟨U, hU, hx⟩ := discrete K x
    have hy : y ∈ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U := by
      rw [Set.mem_preimage, ← hxy]
      change x ∈ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U
      rw [hx]
      exact Set.mem_singleton x
    exact (Set.mem_singleton_iff.mp (hx ▸ hy)).symm
  exact AddMonoidHom.tendsto_coe_cofinite_of_isDiscrete
    (f := (algebraMap K (AdeleRing (𝓞 K) K)).toAddMonoidHom)
    hinj (isDiscrete_range_algebraMap K)
end NumberField.AdeleRing


namespace Units
variable (F D : Type*) [Field F] [Ring D] [Algebra F D]

/-- Conjugation by units, as a linear representation. -/
def conjugationLinear : Dˣ →* (D ≃ₗ[F] D) where
  toFun u := (u.mulLeftLinearEquiv F D).trans (u⁻¹.mulRightLinearEquiv F)
  map_one' := by ext x; simp
  map_mul' u v := by ext x; simp [mul_assoc]

@[simp] theorem conjugationLinear_apply (u : Dˣ) (x : D) :
    conjugationLinear F D u x = (u : D) * x * ↑u⁻¹ := rfl

theorem ker_conjugationLinear [Nontrivial D] [Algebra.IsCentral F D] :
    (conjugationLinear F D).ker =
      (Units.map (algebraMap F D).toMonoidHom).range := by
  ext u
  change conjugationLinear F D u = 1 ↔ ∃ a : Fˣ, Units.map _ a = u
  constructor
  · intro hu
    have hc : (u : D) ∈ Subalgebra.center F D := by
      rw [Subalgebra.mem_center_iff]
      intro x
      have hx := LinearEquiv.congr_fun hu x
      change (u : D) * x * ↑u⁻¹ = x at hx
      have h := congrArg (fun z : D => z * u) hx
      simpa [mul_assoc] using h.symm
    obtain ⟨a, ha⟩ := Algebra.IsCentral.out hc
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact u.ne_zero (by simpa using ha.symm)
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Units.ext
    exact ha
  · rintro ⟨a, rfl⟩
    ext x
    change algebraMap F D (a : F) * x *
      algebraMap F D (↑a⁻¹ : F) = x
    rw [Algebra.commutes, mul_assoc, ← map_mul]
    simp

end Units


open scoped TensorProduct Quaternion
open Module NumberField InfinitePlace

namespace IsQuaternionAlgebra
variable {F D : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
variable [IsTotallyDefinite F D]
variable {ι : Type*} [Fintype ι] (b : Basis ι F D)

omit [NumberField F] [Fintype ι] in
theorem compact_real_conjugation_coefficient (v : InfinitePlace F) (hv : v.IsReal) (i j : ι) :
    ∃ S : Set ℝ, IsCompact S ∧ ∀ u : Dˣ,
      embedding_of_isReal hv (b.repr ((u : D) * b j * ↑u⁻¹) i) ∈ S := by
  let : Algebra F ℝ := (embedding_of_isReal hv).toAlgebra
  obtain ⟨e⟩ := IsTotallyDefinite.cond (D := D) v hv
  let c : Basis ι ℝ ℍ := (b.baseChange ℝ).map e.toLinearEquiv
  let φ : D →+* ℍ := e.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : D →ₐ[F] ℝ ⊗[F] D).toRingHom
  have hc (x : D) : c.repr (φ x) i = embedding_of_isReal hv (b.repr x i) := by
    simp [c, φ, Algebra.smul_def]
    rfl
  refine ⟨(c.coord i) '' Metric.closedBall 0 ‖φ (b j)‖,
    (isCompact_closedBall 0 _).image (c.coord i).continuous_of_finiteDimensional, ?_⟩
  intro u
  refine ⟨φ ((u : D) * b j * ↑u⁻¹), ?_, hc _⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hunit : φ (↑u⁻¹ : D) = (φ (u : D))⁻¹ := by
    simp
  rw [map_mul, map_mul, hunit, norm_mul, norm_mul, norm_inv]
  have hn : ‖φ (u : D)‖ ≠ 0 := norm_ne_zero_iff.mpr (u.map φ.toMonoidHom).ne_zero
  exact le_of_eq (by field_simp)

omit [NumberField F] [Fintype ι] in
theorem compact_infinite_conjugation_coefficient [NumberField.IsTotallyReal F] (i j : ι) :
    ∃ S : Set (InfiniteAdeleRing F), IsCompact S ∧ ∀ u : Dˣ,
      algebraMap F (InfiniteAdeleRing F) (b.repr ((u : D) * b j * ↑u⁻¹) i) ∈ S := by
  classical
  choose S hS hu using fun v : InfinitePlace F =>
    compact_real_conjugation_coefficient b v (IsTotallyReal.isReal v) i j
  let e (v : InfinitePlace F) :=
    Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)
  refine ⟨Set.pi Set.univ (fun v => (e v).symm '' S v), isCompact_univ_pi ?_, ?_⟩
  · intro v
    exact (hS v).image (e v).symm.continuous
  · intro u v hv
    refine ⟨embedding_of_isReal (IsTotallyReal.isReal v)
      (b.repr ((u : D) * b j * ↑u⁻¹) i), hu v u, ?_⟩
    apply (e v).injective
    rw [IsometryEquiv.apply_symm_apply]
    exact (Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal v)
      (WithAbs.toAbs v.1 (b.repr ((u : D) * b j * ↑u⁻¹) i))).symm

end IsQuaternionAlgebra


open scoped TensorProduct NumberField NumberField.AdeleRing FLT
open Module IsDedekindDomain IsQuaternionAlgebra.NumberField
namespace IsQuaternionAlgebra
variable {F D : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
variable [WithRigidification F D]
variable {ι : Type*} [Fintype ι] (b : Basis ι F D)

omit [Fintype ι] in
theorem compact_finite_conjugation_coefficient (T : Set GL₂(𝔸ᶠ[F])) (hT : IsCompact T)
    (i j : ι) :
    ∃ S : Set (𝔸ᶠ[F]), IsCompact S ∧ ∀ u : Dˣ,
      (∃ a ∈ T, ∃ z : (𝔸ᶠ[F])ˣ, WithRigidification.unitsIncl F D u =
        a * Units.map (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])).toMonoidHom z) →
      algebraMap F (𝔸ᶠ[F]) (b.repr ((u : D) * b j * ↑u⁻¹) i) ∈ S := by
  classical
  let e : (𝔸ᶠ[F]) ⊗[F] D ≃ₐ[𝔸ᶠ[F]] M₂(𝔸ᶠ[F]) :=
    AlgEquiv.ofBijective _ WithRigidification.cond
  let c : Basis ι (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]) := (b.baseChange (𝔸ᶠ[F])).map e.toLinearEquiv
  have he (x : D) : e (1 ⊗ₜ[F] x) = WithRigidification.incl x := by
    change algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]) 1 * WithRigidification.incl x = _
    simp
  have hc (x : D) :
      c.repr (WithRigidification.incl x) i = algebraMap F (𝔸ᶠ[F]) (b.repr x i) := by
    rw [← he]
    simp [c, Algebra.smul_def]
  let f : GL₂(𝔸ᶠ[F]) → 𝔸ᶠ[F] :=
    fun a => c.coord i ((a : M₂(𝔸ᶠ[F])) * WithRigidification.incl (b j) * (↑(a⁻¹) : M₂(𝔸ᶠ[F])))
  have hf : Continuous f := by
    exact (IsModuleTopology.continuous_of_linearMap (c.coord i)).comp
      ((Units.continuous_val.mul continuous_const).mul (Units.continuous_val.comp continuous_inv))
  refine ⟨f '' T, hT.image hf, ?_⟩
  intro u hu
  obtain ⟨a, ha, z, hz⟩ := hu
  refine ⟨a, ha, ?_⟩
  rw [← hc]
  change c.coord i _ = c.coord i _
  congr 1
  have hval := congrArg (fun x : GL₂(𝔸ᶠ[F]) => (x : M₂(𝔸ᶠ[F]))) hz
  have hinv := congrArg (fun x : GL₂(𝔸ᶠ[F]) => (↑(x⁻¹) : M₂(𝔸ᶠ[F]))) hz
  change WithRigidification.incl (↑u : D) = _ at hval
  change WithRigidification.incl (↑u⁻¹ : D) = _ at hinv
  rw [map_mul, map_mul, hval, hinv]
  simp only [mul_inv_rev, ← map_inv, Units.val_mul, Units.coe_map]
  have hzX (X : M₂(𝔸ᶠ[F])) :
      algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]) (z : 𝔸ᶠ[F]) *
        (X * algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]) (↑z⁻¹ : 𝔸ᶠ[F])) = X := by
    rw [← mul_assoc, Algebra.commutes, mul_assoc, ← map_mul]
    simp
  simpa only [mul_assoc, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using
    congrArg (fun X : M₂(𝔸ᶠ[F]) => (a : M₂(𝔸ᶠ[F])) * X * (↑(a⁻¹) : M₂(𝔸ᶠ[F])))
      (hzX (WithRigidification.incl (b j))).symm
end IsQuaternionAlgebra

namespace IsQuaternionAlgebra
open Module IsDedekindDomain IsQuaternionAlgebra.NumberField
open scoped NumberField NumberField.AdeleRing FLT
variable {F D : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
variable [IsQuaternionAlgebra F D] [WithRigidification F D]
variable [NumberField.IsTotallyReal F] [IsTotallyDefinite F D]

theorem finiteRelIndex_of_compact_mod_scalars (H : Subgroup Dˣ)
    (T : Set GL₂(𝔸ᶠ[F])) (hT : IsCompact T)
    (hH : ∀ u ∈ H, ∃ a ∈ T, ∃ z : (𝔸ᶠ[F])ˣ,
      WithRigidification.unitsIncl F D u =
        a * Units.map (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])).toMonoidHom z) :
    Subgroup.IsFiniteRelIndex (Units.map (algebraMap F D).toMonoidHom).range H := by
  classical
  let b := Module.finBasis F D
  choose A hA huA using compact_infinite_conjugation_coefficient b
  choose B hB huB using compact_finite_conjugation_coefficient b T hT
  let X (i j : Fin (Module.finrank F D)) : Set F :=
    (algebraMap F (AdeleRing (𝓞 F) F)) ⁻¹' (A i j ×ˢ B i j)
  have hX (i j) : (X i j).Finite :=
    NumberField.AdeleRing.finite_preimage_compact F ((hA i j).prod (hB i j))
  have hu (u : Dˣ) (hu : u ∈ H) (i j) :
      b.repr ((u : D) * b j * ↑u⁻¹) i ∈ X i j :=
    ⟨huA i j u, huB i j u (hH u hu)⟩
  let ρ := Units.conjugationLinear F D
  have hfinite : Finite (H.map ρ) := by
    let f : H.map ρ → ((p : Fin (Module.finrank F D) × Fin (Module.finrank F D)) →
        X p.1 p.2) := fun a p =>
      ⟨b.repr (a.val (b p.2)) p.1, by
        obtain ⟨u, hu', ha⟩ := a.property
        rw [← ha]
        exact hu u hu' p.1 p.2⟩
    have (p : Fin (Module.finrank F D) × Fin (Module.finrank F D)) :
        Finite (X p.1 p.2) := (hX p.1 p.2).to_subtype
    apply Finite.of_injective f
    intro a a' haa
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro j
    apply b.repr.injective
    ext i
    exact congrArg Subtype.val (congrFun haa (i, j))
  rw [← Units.ker_conjugationLinear F D,
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero,
    ← Subgroup.card_map_eq_relIndex_ker]
  exact Nat.card_pos.ne'
end IsQuaternionAlgebra
