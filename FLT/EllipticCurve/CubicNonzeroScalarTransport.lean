/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicNonzeroTransport

/-! # Scalar compatibility of torsion transport

Group homomorphisms commute with scalar multiplication. This compatibility
restricts to nonzero torsion and applies to admissible coordinate changes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable {V W : WeierstrassCurve R} [V.IsElliptic] [W.IsElliptic]
variable (n : ℕ) [NeZero n]

/-- The torsion scalar map is the corresponding power of the identity. -/
theorem torsionScalarIso_hom (W : WeierstrassCurve R) [W.IsElliptic]
    (a : (ZMod n)ˣ) :
    (torsionScalarIso W n a).hom = (𝟙 (torsionModel W n)) ^ a.val.val := rfl

/-- Homomorphisms of torsion groups commute with scalar units. -/
theorem torsionHom_scalar (f : torsionModel V n ⟶ torsionModel W n) [IsMonHom f]
    (a : (ZMod n)ˣ) :
    (torsionScalarIso V n a).hom ≫ f = f ≫ (torsionScalarIso W n a).hom := by
  rw [torsionScalarIso_hom, torsionScalarIso_hom]
  rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]

/-- The scalar action uses the restriction of scalar multiplication. -/
theorem nonzeroTorsionScalarAction_hom (W : WeierstrassCurve R) [W.IsElliptic]
    (a : (ZMod n)ˣ) :
    (nonzeroTorsionScalarAction W n a).hom = nonzeroTorsionScalarHom W n a := rfl

/-- The inverse scalar action is the action of the inverse unit. -/
theorem nonzeroTorsionScalarAction_inv (W : WeierstrassCurve R) [W.IsElliptic]
    (a : (ZMod n)ˣ) :
    (nonzeroTorsionScalarAction W n a).inv = (nonzeroTorsionScalarAction W n a⁻¹).hom := rfl

/-- Transport on nonzero torsion commutes with scalar multiplication. -/
theorem nonzeroTorsionTransport_scalar (e : torsionModel V n ≅ torsionModel W n)
    [IsMonHom e.hom]
    (h0 : torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n)
    (a : (ZMod n)ˣ) :
    (nonzeroTorsionScalarAction V n a).hom ≫
        nonzeroTorsionTransport (V := V) (W := W) n e h0 =
      nonzeroTorsionTransport (V := V) (W := W) n e h0 ≫
        (nonzeroTorsionScalarAction W n a).hom := by
  rw [nonzeroTorsionScalarAction_hom, nonzeroTorsionScalarAction_hom]
  apply (cancel_mono (nonzeroTorsionInclusion W n)).mp
  simp only [Category.assoc, nonzeroTorsionTransport_inclusion,
    nonzeroTorsionScalarHom_inclusion]
  rw [← Category.assoc, nonzeroTorsionScalarHom_inclusion, Category.assoc,
    torsionHom_scalar, ← Category.assoc,
    ← nonzeroTorsionTransport_inclusion (V := V) (W := W) n e h0, Category.assoc]

/-- The coordinate-change isomorphism is the restricted torsion transport. -/
theorem variableChangeNonzeroTorsionIso_hom (W : WeierstrassCurve R) [W.IsElliptic]
    (C : VariableChange R) :
    (variableChangeNonzeroTorsionIso n W C).hom =
      nonzeroTorsionTransport (V := C • W) (W := W) n (variableChangeTorsionIso W C n)
        (torsionIso_zero (V := C • W) (W := W) n (variableChangeTorsionIso W C n)) := rfl

/-- Coordinate changes intertwine the inverse scalar actions on nonzero torsion. -/
theorem variableChangeNonzeroTorsionIso_scalar (W : WeierstrassCurve R) [W.IsElliptic]
    (C : VariableChange R) (a : (ZMod n)ˣ) :
    (nonzeroTorsionScalarAction (C • W) n a).inv ≫
        (variableChangeNonzeroTorsionIso n W C).hom =
      (variableChangeNonzeroTorsionIso n W C).hom ≫
        (nonzeroTorsionScalarAction W n a).inv := by
  rw [nonzeroTorsionScalarAction_inv, nonzeroTorsionScalarAction_inv,
    variableChangeNonzeroTorsionIso_hom]
  exact nonzeroTorsionTransport_scalar (V := C • W) (W := W) n
    (variableChangeTorsionIso W C n)
    (torsionIso_zero (V := C • W) (W := W) n (variableChangeTorsionIso W C n)) a⁻¹
end WeierstrassCurve.CubicCharts
