/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionIdeal
public import Mathlib.LinearAlgebra.Prod

/-!
# One original linear system for all boundary corrections

The unknown consists of one original scalar and one shared family of chart
corrections. The target retains every boundary equation and every full mixed
equation. Its kernel projects onto the unchanged correction ideal.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)

local notation "α" => fun i ↦ algebraMap R (A i)
set_option quotPrecheck false in
local notation "hα" => fun i j r ↦ ((p i j).commutes r).trans ((q i j).commutes r).symm

/-- One linear map retains the boundary kernels and all simultaneous mixed equations. -/
def correctionSystem : (R × ∀ i, A i) →ₗ[R] ((∀ i, B i) × ∀ i j, C i j) where
  toFun x := (fun i ↦ φ i (x.2 i), fun i j ↦
    p i j (x.2 i) - q i j (x.2 j) - p i j (α i x.1) * (p i j (u i) - q i j (u j)))
  map_add' x y := by
    apply Prod.ext
    · funext i
      exact map_add _ _ _
    · funext i j
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]
      ring
  map_smul' r x := by
    apply Prod.ext
    · funext i
      exact (φ i).toLinearMap.map_smul r (x.2 i)
    · funext i j
      change p i j (r • x.2 i) - q i j (r • x.2 j) -
        p i j (α i (r * x.1)) * (p i j (u i) - q i j (u j)) =
        r • (p i j (x.2 i) - q i j (x.2 j) -
          p i j (α i x.1) * (p i j (u i) - q i j (u j)))
      simp only [map_mul, AlgHom.commutes, Algebra.smul_def]
      ring

/-- The actual module of scalar and simultaneous original correction pairs. -/
abbrev correctionSolutions := LinearMap.ker (correctionSystem φ p q u)

/-- Kernel membership means the exact original equations, including the boundary kernels. -/
theorem mem_correctionSolutions (x : R × ∀ i, A i) :
    x ∈ correctionSolutions φ p q u ↔
      (∀ i, φ i (x.2 i) = 0) ∧ ∀ i j,
        p i j (x.2 i) - q i j (x.2 j) =
          p i j (α i x.1) * (p i j (u i) - q i j (u j)) := by
  change (fun i ↦ φ i (x.2 i), fun i j ↦ _) = (0, 0) ↔ _
  simp only [Prod.mk.injEq, funext_iff, Pi.zero_apply, sub_eq_zero]

/-- Project a simultaneous solution to its original scalar. -/
def correctionMultiplier : correctionSolutions φ p q u →ₗ[R] R :=
  (LinearMap.fst R R (∀ i, A i)).comp (correctionSolutions φ p q u).subtype

/-- Every projected scalar solves the unchanged full correction problem. -/
theorem correctionMultiplier_mem (x : correctionSolutions φ p q u) :
    correctionMultiplier φ p q u x ∈ ideal α (fun i ↦ (φ i).toRingHom)
      (fun i j ↦ (p i j).toRingHom) (fun i j ↦ (q i j).toRingHom) hα u :=
  ⟨x.val.2, (mem_correctionSolutions φ p q u x.val).mp x.property⟩

/-- The image of the original solution module is exactly the original correction ideal. -/
theorem range_correctionMultiplier :
    LinearMap.range (correctionMultiplier φ p q u) = ideal α (fun i ↦ (φ i).toRingHom)
      (fun i j ↦ (p i j).toRingHom) (fun i j ↦ (q i j).toRingHom) hα u := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    exact correctionMultiplier_mem φ p q u x
  · rintro ⟨z, hz, he⟩
    exact ⟨⟨(r, z), (mem_correctionSolutions φ p q u (r, z)).mpr ⟨hz, he⟩⟩, rfl⟩

end FLT.Mazur.BoundaryCorrectionIdeal
