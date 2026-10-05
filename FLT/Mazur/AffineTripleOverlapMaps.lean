/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOverlapPullback

/-!
# The three projections of the affine triple overlap

The triple tensor ring is parenthesized as `S ⊗[R] (S ⊗[R] S)`.
Each pair projection is identified with the corresponding actual morphism
into the scheme fiber product, by checking its two projections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
universe u
namespace FLT.Mazur.AffineTripleOverlapMaps
open AffineOverlapTensor
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The coordinate ring of the triple overlap. -/
abbrev Triple := S ⊗[R] (S ⊗[R] S)

/-- Retain the first two coordinates. -/
def pair12 : S ⊗[R] S →ₐ[R] Triple R S :=
  Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeLeft

/-- Retain the last two coordinates. -/
def pair23 : S ⊗[R] S →ₐ[R] Triple R S := Algebra.TensorProduct.includeRight

/-- Retain the first and last coordinates. -/
def pair13 : S ⊗[R] S →ₐ[R] Triple R S :=
  Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight

@[simp]
theorem pair12_tmul (s t : S) : pair12 R S (s ⊗ₜ[R] t) = s ⊗ₜ[R] (t ⊗ₜ[R] 1) := rfl

@[simp]
theorem pair23_tmul (s t : S) : pair23 R S (s ⊗ₜ[R] t) = 1 ⊗ₜ[R] (s ⊗ₜ[R] t) := rfl

@[simp]
theorem pair13_tmul (s t : S) : pair13 R S (s ⊗ₜ[R] t) = s ⊗ₜ[R] (1 ⊗ₜ[R] t) := rfl

/-- The first coordinate inclusion. -/
abbrev coord1 : S →+* Triple R S := Algebra.TensorProduct.includeLeftRingHom

/-- The middle coordinate inclusion. -/
abbrev coord2 : S →+* Triple R S := (pair23 R S).toRingHom.comp (left R S)

/-- The last coordinate inclusion. -/
abbrev coord3 : S →+* Triple R S := (pair23 R S).toRingHom.comp (right R S)

/-- The first projection of the first pair is the first coordinate. -/
theorem pair12_left : (pair12 R S).toRingHom.comp (left R S) = coord1 R S := by
  ext s
  simp [left, coord1, pair12, Algebra.TensorProduct.one_def]

/-- The second projection of the first pair is the middle coordinate. -/
theorem pair12_right : (pair12 R S).toRingHom.comp (right R S) = coord2 R S := rfl

/-- The first projection of the last pair is the middle coordinate. -/
theorem pair23_left : (pair23 R S).toRingHom.comp (left R S) = coord2 R S := rfl

/-- The second projection of the last pair is the last coordinate. -/
theorem pair23_right : (pair23 R S).toRingHom.comp (right R S) = coord3 R S := rfl

/-- The first projection of the outer pair is the first coordinate. -/
theorem pair13_left : (pair13 R S).toRingHom.comp (left R S) = coord1 R S := by
  ext s
  simp [left, coord1, pair13, Algebra.TensorProduct.one_def]

/-- The second projection of the outer pair is the last coordinate. -/
theorem pair13_right : (pair13 R S).toRingHom.comp (right R S) = coord3 R S := rfl

/-- Composition of affine scheme maps follows composition of their ring maps. -/
theorem spec_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (w : g.comp f = h) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom w)

/-- The pair map to the tensor spectrum agrees with the actual fiber-product lift. -/
theorem pair_chart (p : S ⊗[R] S →ₐ[R] Triple R S) :
    Spec.map (CommRingCat.ofHom p.toRingHom) ≫ (pullbackSpecIso R S S).inv =
      Limits.pullback.lift
        (Spec.map (CommRingCat.ofHom p.toRingHom) ≫ Spec.map (CommRingCat.ofHom (left R S)))
        (Spec.map (CommRingCat.ofHom p.toRingHom) ≫ Spec.map (CommRingCat.ofHom (right R S)))
        (by
          rw [Category.assoc, Category.assoc, ← pullbackSpecIso_inv_fst R S S,
            ← pullbackSpecIso_inv_snd R S S, Category.assoc, Category.assoc,
            Limits.pullback.condition]) := by
  apply Limits.pullback.hom_ext <;> simp

end FLT.Mazur.AffineTripleOverlapMaps
