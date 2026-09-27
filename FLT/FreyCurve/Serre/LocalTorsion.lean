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
/-- Triviality of the coordinate action after extending the ground field implies
triviality of the restricted representation on geometric torsion. -/
theorem galoisRep_map_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] [DecidableEq (AlgebraicClosure L)]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : 0 < n) (σ : Field.absoluteGaloisGroup L)
    (hσ : ∀ P : (E⁄(AlgebraicClosure L)).Point, n • P = 0 →
      Affine.Point.map (σ.toAlgHom.restrictScalars K) P = P) :
    (E.galoisRep n hn).map (algebraMap K L) σ = 1 := by
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
    rw [hp, map_zero]
  change φ (Affine.Point.map (W' := E) g.toAlgHom P₀) = φ P₀
  rw [heq]
  exact hσ (φ P₀) ht

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

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [DecidableEq (AlgebraicClosure K)] [DecidableEq (AlgebraicClosure L)]

set_option backward.isDefEq.respectTransparency false in
/-- The chosen embedding of algebraic closures induces a linear map on geometric torsion. -/
noncomputable def geometricTorsionBaseChange (E : WeierstrassCurve K) (n : ℕ) :
    (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n →ₗ[ZMod n]
      ((E.map (algebraMap K L)).map (algebraMap L (AlgebraicClosure L))).nTorsion n := by
  let f : AlgebraicClosure K →ₐ[K] AlgebraicClosure L :=
    { __ := AlgebraicClosure.map (algebraMap K L)
      commutes' := AlgebraicClosure.map_algebraMap _ }
  exact AddMonoidHom.toZModLinearMap n
    { toFun := fun P ↦ ⟨Affine.Point.map (W' := E) f P.val, by
        change (n : ℤ) • Affine.Point.map (W' := E) f P.val = 0
        rw [← map_zsmul, show (n : ℤ) • P.val = 0 from P.property, map_zero]⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun P Q ↦ Subtype.ext (map_add _ P.val Q.val) }

set_option backward.isDefEq.respectTransparency false in
/-- Extension of algebraic closures is injective on geometric torsion. -/
theorem geometricTorsionBaseChange_injective (E : WeierstrassCurve K) (n : ℕ) :
    Function.Injective (E.geometricTorsionBaseChange (L := L) n) := by
  intro P Q h
  apply Subtype.ext
  exact Affine.Point.map_injective (W' := E)
    (show AlgebraicClosure K →ₐ[K] AlgebraicClosure L from
      { __ := AlgebraicClosure.map (algebraMap K L)
        commutes' := AlgebraicClosure.map_algebraMap _ }) (congrArg Subtype.val h)

set_option backward.isDefEq.respectTransparency false in
/-- Geometric torsion commutes with extension of characteristic-zero fields.
Surjectivity uses the existing general torsion-cardinality theorem. -/
theorem geometricTorsionBaseChange_bijective [CharZero K]
    (E : WeierstrassCurve K) [E.IsElliptic] {n : ℕ} (hn : 0 < n) :
    Function.Bijective (E.geometricTorsionBaseChange (L := L) n) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let : Finite ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) :=
    (E.map (algebraMap K (AlgebraicClosure K))).n_torsion_finite hn
  let : Finite (((E.map (algebraMap K L)).map (algebraMap L (AlgebraicClosure L))).nTorsion n) :=
    ((E.map (algebraMap K L)).map (algebraMap L (AlgebraicClosure L))).n_torsion_finite hn
  apply (E.geometricTorsionBaseChange_injective (L := L) n).bijective_of_nat_card_le
  rw [(E.map (algebraMap K (AlgebraicClosure K))).n_torsion_card (by exact_mod_cast hn.ne'),
    ((E.map (algebraMap K L)).map (algebraMap L (AlgebraicClosure L))).n_torsion_card
      (by exact_mod_cast hn.ne')]

set_option backward.isDefEq.respectTransparency false in
/-- The torsion comparison intertwines restriction of Galois representations. -/
theorem geometricTorsionBaseChange_equivariant [DecidableEq K] [DecidableEq L]
    (E : WeierstrassCurve K) [E.IsElliptic] (n : ℕ) (hn : 0 < n)
    (σ : Field.absoluteGaloisGroup L)
    (P : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) :
    E.geometricTorsionBaseChange (L := L) n ((E.galoisRep n hn).map (algebraMap K L) σ P) =
      (E.map (algebraMap K L)).galoisRep n hn σ (E.geometricTorsionBaseChange (L := L) n P) := by
  let f : AlgebraicClosure K →ₐ[K] AlgebraicClosure L :=
    { __ := AlgebraicClosure.map (algebraMap K L)
      commutes' := AlgebraicClosure.map_algebraMap _ }
  let g := Field.absoluteGaloisGroup.map (algebraMap K L) σ
  apply Subtype.ext
  change Affine.Point.map (W' := E) f (Affine.Point.map (W' := E) g.toAlgHom P.val) =
    Affine.Point.map (W' := E.map (algebraMap K L)) σ.toAlgHom
      (Affine.Point.map (W' := E) f P.val)
  cases P.val with
  | zero => rfl
  | some x y h =>
    apply Affine.Point.some_eq_some <;> exact Field.absoluteGaloisGroup.lift_map _ _ _

end WeierstrassCurve
