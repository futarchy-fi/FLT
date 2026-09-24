/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.Velu

/-!
# Vélu's coordinate map

The coordinate functions are the finite sums of translates from Vélu's construction.
They are constant on kernel cosets and commute with the Galois action. Turning them into
points on the candidate curve still requires the nonsingularity and curve-equation proofs.
-/

@[expose] public section

noncomputable section

open scoped BigOperators WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

section Sums

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable (G : AddSubgroup A) [Fintype G]

/-- The sum of coordinate differences over a finite subgroup, including its identity. -/
def sumCoord (f : A → B) (P : A) : B :=
  ∑ Q : G, (f (P + Q.val) - f Q.val)

/-- A sum of translates is unchanged on translating its argument by a kernel point. -/
theorem sumCoord_add (f : A → B) (P : A) (R : G) :
    sumCoord G f (P + R.val) = sumCoord G f P := by
  simp only [sumCoord, Finset.sum_sub_distrib]
  congr 1
  have h := Equiv.sum_comp (Equiv.addLeft R) (fun Q : G ↦ f (P + Q.val))
  simpa only [Equiv.coe_addLeft, AddSubgroup.coe_add, add_assoc] using h

/-- The sum of differences vanishes at the identity. -/
theorem sumCoord_zero (f : A → B) : sumCoord G f 0 = 0 := by
  simp [sumCoord]

/-- The sum of differences vanishes throughout the kernel. -/
theorem sumCoord_of_mem (f : A → B) {P : A} (hP : P ∈ G) :
    sumCoord G f P = 0 := by
  simpa only [zero_add, sumCoord_zero] using sumCoord_add G f 0 ⟨P, hP⟩

end Sums

section Coordinates

variable {K : Type*} [Field K] [DecidableEq K]
variable (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- Vélu's x-coordinate, with the identity term providing the original x-coordinate. -/
def xMap (P : E.toAffine.Point) : K := sumCoord G xCoord P

/-- Vélu's y-coordinate, with the identity term providing the original y-coordinate. -/
def yMap (P : E.toAffine.Point) : K := sumCoord G yCoord P

/-- Vélu's x-coordinate is constant on each kernel coset. -/
theorem xMap_add (P : E.toAffine.Point) (Q : G) :
    xMap E G (P + Q.val) = xMap E G P := sumCoord_add G xCoord P Q

/-- Vélu's y-coordinate is constant on each kernel coset. -/
theorem yMap_add (P : E.toAffine.Point) (Q : G) :
    yMap E G (P + Q.val) = yMap E G P := sumCoord_add G yCoord P Q

/-- Vélu's point function, conditional on nonsingularity of its coordinates away from the kernel.
Kernel points go to infinity. This definition does not supply the missing landing proof. -/
def pointMap (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (P : E.toAffine.Point) : E'.toAffine.Point := by
  classical
  exact if hP : P ∈ G then 0 else .some _ _ (h P hP)

/-- Once the coordinate map lands on the target, its zero fiber is exactly the chosen kernel. -/
theorem pointMap_eq_zero_iff (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (P : E.toAffine.Point) : pointMap E G E' h P = 0 ↔ P ∈ G := by
  classical
  by_cases hP : P ∈ G <;> simp [pointMap, hP, Affine.Point.some_ne_zero]

/-- The conditional point map takes the identity to the identity. -/
theorem pointMap_zero (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P)) :
    pointMap E G E' h 0 = 0 :=
  (pointMap_eq_zero_iff E G E' h 0).mpr G.zero_mem

/-- The conditional point map is constant on each kernel coset. -/
theorem pointMap_add_kernel (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (P : E.toAffine.Point) (Q : G) :
    pointMap E G E' h (P + Q.val) = pointMap E G E' h P := by
  classical
  have hmem : P + Q.val ∈ G ↔ P ∈ G := G.add_mem_cancel_right Q.property
  by_cases hP : P ∈ G
  · simp [pointMap, hP, hmem.mpr hP]
  · simp only [pointMap, dite_eq_right hP, dite_eq_right (hmem.not.mpr hP),
      xMap_add, yMap_add]

end Coordinates

section Galois

variable {K L : Type*} [Field K] [Field L] [DecidableEq L] [Algebra K L]
variable (E : WeierstrassCurve K) (G : AddSubgroup (E⁄L).Point)

/-- The permutation of a Galois-stable subgroup induced by a field automorphism. -/
def subgroupEquiv (σ : L ≃ₐ[K] L)
    (hG : ∀ (τ : L ≃ₐ[K] L) P, P ∈ G → Affine.Point.map (W' := E) τ.toAlgHom P ∈ G) :
    G ≃ G where
  toFun P := ⟨Affine.Point.map (W' := E) σ.toAlgHom P.val, hG σ _ P.property⟩
  invFun P := ⟨Affine.Point.map (W' := E) σ.symm.toAlgHom P.val, hG σ.symm _ P.property⟩
  left_inv P := by
    apply Subtype.ext
    rcases P with ⟨P, _⟩
    cases P <;> simp only [Affine.Point.map, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
    all_goals rfl
  right_inv P := by
    apply Subtype.ext
    rcases P with ⟨P, _⟩
    cases P <;> simp only [Affine.Point.map, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    all_goals rfl

/-- A sum of translates of an equivariant coordinate remains equivariant. -/
theorem sumCoord_map [Fintype G]
    (hG : ∀ (τ : L ≃ₐ[K] L) P, P ∈ G → Affine.Point.map (W' := E) τ.toAlgHom P ∈ G)
    (σ : L ≃ₐ[K] L) (f : (E⁄L).Point → L)
    (hf : ∀ P, f (Affine.Point.map (W' := E) σ.toAlgHom P) = σ (f P))
    (P : (E⁄L).Point) :
    sumCoord G f (Affine.Point.map (W' := E) σ.toAlgHom P) = σ (sumCoord G f P) := by
  rw [sumCoord, sumCoord, map_sum]
  calc
    _ = ∑ Q : G, (f (Affine.Point.map (W' := E) σ.toAlgHom P +
        (subgroupEquiv E G σ hG Q).val) - f (subgroupEquiv E G σ hG Q).val) :=
      ((subgroupEquiv E G σ hG).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Q _
      change f (Affine.Point.map (W' := E) σ.toAlgHom P +
        Affine.Point.map (W' := E) σ.toAlgHom Q.val) -
        f (Affine.Point.map (W' := E) σ.toAlgHom Q.val) = _
      rw [← map_add, hf, hf, map_sub]

/-- Vélu's x-coordinate commutes with Galois on a stable finite kernel. -/
theorem xMap_map [Fintype G]
    (hG : ∀ (τ : L ≃ₐ[K] L) P, P ∈ G → Affine.Point.map (W' := E) τ.toAlgHom P ∈ G)
    (σ : L ≃ₐ[K] L) (P : (E⁄L).Point) :
    xMap (E⁄L) G (Affine.Point.map (W' := E) σ.toAlgHom P) = σ (xMap (E⁄L) G P) :=
  sumCoord_map E G hG σ xCoord (xCoord_map E σ) P

/-- Vélu's y-coordinate commutes with Galois on a stable finite kernel. -/
theorem yMap_map [Fintype G]
    (hG : ∀ (τ : L ≃ₐ[K] L) P, P ∈ G → Affine.Point.map (W' := E) τ.toAlgHom P ∈ G)
    (σ : L ≃ₐ[K] L) (P : (E⁄L).Point) :
    yMap (E⁄L) G (Affine.Point.map (W' := E) σ.toAlgHom P) = σ (yMap (E⁄L) G P) :=
  sumCoord_map E G hG σ yCoord (yCoord_map E σ) P

/-- Membership of a Galois-stable kernel is preserved in both directions by Galois. -/
theorem map_mem_iff
    (hG : ∀ (τ : L ≃ₐ[K] L) P, P ∈ G → Affine.Point.map (W' := E) τ.toAlgHom P ∈ G)
    (σ : L ≃ₐ[K] L) (P : (E⁄L).Point) :
    Affine.Point.map (W' := E) σ.toAlgHom P ∈ G ↔ P ∈ G := by
  refine ⟨fun hP ↦ ?_, hG σ P⟩
  have h := hG σ.symm _ hP
  have hinv : Affine.Point.map (W' := E) σ.symm.toAlgHom
      (Affine.Point.map (W' := E) σ.toAlgHom P) = P := by
    cases P <;> simp only [Affine.Point.map, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
    all_goals rfl
  rwa [hinv] at h

/-- Once Vélu's coordinates land on a target defined over the base field, the resulting point
map commutes with Galois. No additivity or nonsingularity theorem is assumed implicitly. -/
theorem pointMap_map [Fintype G] (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → (E'⁄L).Nonsingular (xMap (E⁄L) G P) (yMap (E⁄L) G P))
    (hG : ∀ (τ : L ≃ₐ[K] L) P, P ∈ G → Affine.Point.map (W' := E) τ.toAlgHom P ∈ G)
    (σ : L ≃ₐ[K] L) (P : (E⁄L).Point) :
    pointMap (E⁄L) G (E'⁄L) h (Affine.Point.map (W' := E) σ.toAlgHom P) =
      Affine.Point.map (W' := E') σ.toAlgHom (pointMap (E⁄L) G (E'⁄L) h P) := by
  classical
  by_cases hP : P ∈ G
  · simp [pointMap, hP, hG σ P hP]
  · have hm := (map_mem_iff E G hG σ P).not.mpr hP
    simp only [pointMap, dite_eq_right hP, dite_eq_right hm, Affine.Point.map_some,
      Affine.Point.some.injEq]
    exact ⟨xMap_map E G hG σ P, yMap_map E G hG σ P⟩

end Galois

end WeierstrassCurve.Velu
