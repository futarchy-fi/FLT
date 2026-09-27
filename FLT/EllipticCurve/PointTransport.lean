/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
/-!
# Transporting point groups along field maps

These maps use an explicit ring homomorphism, so that no auxiliary algebra structure
or redundant self-base-change occurs in their source and target types.
-/

@[expose] public section

namespace WeierstrassCurve.Affine.Point
variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
  (W : WeierstrassCurve F)
/-- A field homomorphism induces the coordinatewise homomorphism of point groups. -/
noncomputable def mapRingHom (f : F →+* L) : W.toAffine.Point →+
    (W.map f).toAffine.Point where
  toFun
    | .zero => .zero
    | .some x y h => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right]
      change 0 = _ + _
      rw [add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, W.toAffine.map_negY])]
    · simp only [add_some hxy]
      have hxy' : ¬ (f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
        rw [W.toAffine.map_negY]
        exact fun h => hxy ⟨f.injective h.1, f.injective h.2⟩
      change some _ _ _ = some _ _ _ + some _ _ _
      rw [add_some hxy']
      congr 1
      · exact (by rw [W.toAffine.map_slope, W.toAffine.map_addX])
      · exact (by rw [W.toAffine.map_slope, W.toAffine.map_addY])
/-- A field isomorphism induces an isomorphism of point groups. -/
noncomputable def mapRingEquiv (f : F ≃+* L) : W.toAffine.Point ≃+
    (W.map (f : F →+* L)).toAffine.Point :=
  AddEquiv.ofBijective (mapRingHom W (f : F →+* L)) ⟨by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) he
    any_goals contradiction
    · rfl
    · have he' := some.inj he
      have hx := f.injective he'.1
      have hy := f.injective he'.2
      exact some_eq_some _ hx hy,
    by
      rintro (_ | ⟨x, y, h⟩)
      · exact ⟨0, rfl⟩
      · have h' : W.toAffine.Nonsingular (f.symm x) (f.symm y) := by
          apply (W.toAffine.map_nonsingular (f := (f : F →+* L)) f.injective _ _).mp
          change (W.map (f : F →+* L)).toAffine.Nonsingular (f (f.symm x)) (f (f.symm y))
          simpa only [f.apply_symm_apply] using h
        refine ⟨.some _ _ h', ?_⟩
        change some _ _ _ = some _ _ _
        exact some_eq_some _ (f.apply_symm_apply _) (f.apply_symm_apply _)⟩

/-- The point-group isomorphism applies the field isomorphism to both coordinates. -/
@[simp] theorem mapRingEquiv_some (f : F ≃+* L) {x y : F} (h : W.toAffine.Nonsingular x y) :
    mapRingEquiv W f (.some _ _ h) =
      .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

end WeierstrassCurve.Affine.Point
