/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Torsion
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Comparing geometric torsion after extending the ground field

The chosen embedding of algebraic closures intertwines the coordinate action
with restriction of the Galois representation. Injectivity transfers unipotence.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

set_option backward.isDefEq.respectTransparency false in
/-- Square-unipotence of the coordinate action after a field extension implies
square-unipotence of the restricted representation on the original geometric torsion. -/
theorem galoisRep_map_sub_one_sq_eq_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] [DecidableEq (AlgebraicClosure L)]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : 0 < n) (σ : Field.absoluteGaloisGroup L)
    (hσ : ∀ P : (E⁄(AlgebraicClosure L)).Point, n • P = 0 →
      Affine.Point.map (σ.toAlgHom.restrictScalars K)
        (Affine.Point.map (σ.toAlgHom.restrictScalars K) P - P) -
        (Affine.Point.map (σ.toAlgHom.restrictScalars K) P - P) = 0) :
    ((E.galoisRep n hn).map (algebraMap K L) σ - 1) ^ 2 = 0 := by
  let f : AlgebraicClosure K →ₐ[K] AlgebraicClosure L :=
    { __ := AlgebraicClosure.map (algebraMap K L)
      commutes' := AlgebraicClosure.map_algebraMap _ }
  let g := Field.absoluteGaloisGroup.map (algebraMap K L) σ
  let φ := Affine.Point.map (W' := E) f
  have heq (P : (E⁄(AlgebraicClosure K)).Point) :
      φ (Affine.Point.map (W' := E) g.toAlgHom P) =
        Affine.Point.map (σ.toAlgHom.restrictScalars K) (φ P) := by
    cases P with
    | zero => rfl
    | some x y h =>
      apply Affine.Point.some_eq_some <;> exact Field.absoluteGaloisGroup.lift_map _ _ _
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  apply Affine.Point.map_injective (W' := E) f
  let P₀ : (E⁄(AlgebraicClosure K)).Point := P.val
  have ht : n • φ P₀ = 0 := by
    rw [← map_nsmul]
    have hp : n • P₀ = 0 := by
      simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property
    rw [hp,map_zero]
  have H := hσ (φ P₀) ht
  change φ (Affine.Point.map (W' := E) g.toAlgHom
    (Affine.Point.map (W' := E) g.toAlgHom P₀ - P₀) -
    (Affine.Point.map (W' := E) g.toAlgHom P₀ - P₀)) = φ 0
  simpa only [map_sub, map_zero, heq] using H
end WeierstrassCurve
