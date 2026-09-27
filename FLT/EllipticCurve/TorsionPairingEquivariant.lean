/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CoefficientAction
public import FLT.EllipticCurve.TorsionPairingBilinear
/-!
# Equivariance of the torsion pairing

Transporting a regular torsion function and its multiplication root under a
coefficient automorphism transports their translation ratio. Independence
of the chosen root data then gives equivariance of the constructed pairing.
-/

@[expose] public section

open Polynomial
open scoped nonZeroDivisors WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (E : Affine K)
  [E.IsElliptic] [IsAlgClosed F] [DecidableEq F]
local instance : (E⁄F).IsElliptic :=
  inferInstanceAs (E.map (algebraMap K F)).IsElliptic
/-- Field automorphisms act on the kernel of multiplication. -/
noncomputable def torsionKernelMap (σ : F ≃ₐ[K] F) (n : ℕ) :
    Point.torsionKernel (E⁄F) n →+ Point.torsionKernel (E⁄F) n where
  toFun T := ⟨Point.map (W' := E) σ.toAlgHom T.val, by
    change n • Point.map σ.toAlgHom T.val = 0
    rw [← map_nsmul, show n • T.val = 0 from T.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' S T := Subtype.ext (map_add _ _ _)
set_option backward.isDefEq.respectTransparency false in
/-- Applying an automorphism to both points applies it to their pairing value. -/
theorem torsionPairing_equivariant (σ : F ≃ₐ[K] F) {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (S T : Point.torsionKernel (E⁄F) n) :
    ((torsionPairing (E⁄F) hn hchar (torsionKernelMap E σ n S)
      (torsionKernelMap E σ n T)).toMul.val : F) =
      σ ((torsionPairing (E⁄F) hn hchar S T).toMul.val : F) := by
  rcases T with ⟨T, hT⟩
  cases T with
  | zero =>
    change ((torsionPairingBilinear (E⁄F) hn hchar (torsionKernelMap E σ n S)
      (torsionKernelMap E σ n 0)).toMul.val : F) =
        σ ((torsionPairingBilinear (E⁄F) hn hchar S 0).toMul.val : F)
    simp only [map_zero]
    exact (map_one σ).symm
  | some x y ht =>
    obtain ⟨f, hf0, hf⟩ := Point.exists_torsionFunction ht n hT
    obtain ⟨g, hg0, hg⟩ := exists_pow_eq_nsmulPullback (E⁄F) hn hchar ht hf0 hf
    let r : TorsionRoot (E⁄F) n hn (Point.some x y ht) :=
      ⟨(algebraMap (E⁄F).CoordinateRing (E⁄F).FunctionField f, g), by
        rw [Point.fractionalIdeal_some, CoordinateRing.XYIdeal'_eq,
          ← FractionalIdeal.coeIdeal_pow, hf, FractionalIdeal.coeIdeal_span_singleton], hg0, hg⟩
    have hfσ : CoordinateRing.XYIdeal (E⁄F) (σ x) (C (σ y)) ^ n =
        Ideal.span {coefficientCoordinate E σ f} := by
      rw [← coefficientCoordinate_XYIdeal, ← Ideal.map_pow, hf,
        Ideal.map_span, Set.image_singleton]
      rfl
    have hgσ : (coefficientHom E σ g) ^ n =
        nsmulPullback (E⁄F) n hn (algebraMap (E⁄F).CoordinateRing (E⁄F).FunctionField
          (coefficientCoordinate E σ f)) := by
      rw [← map_pow, hg, coefficientHom_nsmulPullback, coefficientCoordinate_compat]
    let Tσ := torsionKernelMap E σ n ⟨Point.some x y ht, hT⟩
    let rσ : TorsionRoot (E⁄F) n hn Tσ.val :=
      ⟨(algebraMap (E⁄F).CoordinateRing (E⁄F).FunctionField (coefficientCoordinate E σ f),
        coefficientHom E σ g), by
        rw [show Tσ.val = Point.map (W' := E) σ.toAlgHom (Point.some x y ht) from rfl,
          Point.map_some, Point.fractionalIdeal_some, CoordinateRing.XYIdeal'_eq,
          ← FractionalIdeal.coeIdeal_pow]
        change FractionalIdeal.spanSingleton (E⁄F).CoordinateRing⁰
            (algebraMap (E⁄F).CoordinateRing (E⁄F).FunctionField (coefficientCoordinate E σ f)) =
          (↑(CoordinateRing.XYIdeal (E⁄F) (σ x) (C (σ y)) ^ n) :
            FractionalIdeal (E⁄F).CoordinateRing⁰ (E⁄F).FunctionField)
        rw [hfσ, FractionalIdeal.coeIdeal_span_singleton],
        (_root_.map_ne_zero _).mpr hg0, hgσ⟩
    apply (algebraMap F (E⁄F).FunctionField).injective
    rw [← coefficientHom_const E σ,
      torsionPairing_eq_ratio (E⁄F) hn hchar _ _ rσ,
      torsionPairing_eq_ratio (E⁄F) hn hchar _ _ r]
    change translationPullback (E⁄F) (Point.map (W' := E) σ.toAlgHom S.val)
        (coefficientHom E σ g) / coefficientHom E σ g =
      coefficientHom E σ (translationPullback (E⁄F) S.val g / g)
    rw [map_div₀, coefficientHom_translation]
end WeierstrassCurve.Affine.FunctionField
