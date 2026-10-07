/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInvariantTransport
public import FLT.EllipticCurve.CubicNonzeroScalarTransport

/-! # Coordinate transport of cyclic parameters

An equivariant isomorphism of nonzero torsion schemes induces an isomorphism
of their scalar-invariant coordinate rings and hence of their scalar quotients.
The resulting scheme isomorphism commutes with forgetting the generator.
In particular, admissible Weierstrass coordinate changes preserve these parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable {V W : WeierstrassCurve R} [V.IsElliptic] [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

/-- The canonical affine presentation of the nonzero torsion parameter scheme. -/
def nonzeroTorsionCoordinatePresentation (W : WeierstrassCurve R) [W.IsElliptic] (n : ℕ)
    [NeZero n] [Fact (IsUnit (n : R))] :
    nonzeroTorsionModel W n ≅
      (algSpec (.of R)).obj (op (CommAlgCat.of R (NonzeroTorsionRing W n))) :=
  (nonzeroTorsionModel W n).left.isoSpec.asOver (Spec (.of R))

/-- Coordinate pullback along an isomorphism of nonzero torsion schemes. -/
def nonzeroTorsionCoordinateTransport
    (e : nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n) :
    NonzeroTorsionRing W n ≃ₐ[R] NonzeroTorsionRing V n :=
  affineCoordinateIso (NonzeroTorsionRing V n) (NonzeroTorsionRing W n)
    (nonzeroTorsionModel V n) (nonzeroTorsionModel W n)
    (nonzeroTorsionCoordinatePresentation V n)
    (nonzeroTorsionCoordinatePresentation W n) e

theorem nonzeroTorsionCoordinateTransport_equivariant
    (e : nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n)
    (he : ∀ a : (ZMod n)ˣ, (nonzeroTorsionScalarAction V n a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction W n a).inv)
    (a : (ZMod n)ˣ) (x : NonzeroTorsionRing W n) :
    nonzeroTorsionCoordinateTransport (V := V) (W := W) n e (a • x) =
      a • nonzeroTorsionCoordinateTransport (V := V) (W := W) n e x := by
  have h := affineCoordinateIso_commutes
    (NonzeroTorsionRing V n) (NonzeroTorsionRing W n)
    (nonzeroTorsionModel V n) (nonzeroTorsionModel W n)
    (nonzeroTorsionCoordinatePresentation V n)
    (nonzeroTorsionCoordinatePresentation W n) e
    (nonzeroTorsionScalarAction V n a) (nonzeroTorsionScalarAction W n a) (he a)
  exact congrArg (fun f : NonzeroTorsionRing W n →ₐ[R] NonzeroTorsionRing V n => f x) h

/-- Scalar-equivariant isomorphisms identify the actual invariant coordinate algebras. -/
def scalarInvariantTransport
    (e : nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n)
    (he : ∀ a : (ZMod n)ˣ, (nonzeroTorsionScalarAction V n a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction W n a).inv) :
    TorsionScalarInvariantRing W n ≃ₐ[R] TorsionScalarInvariantRing V n :=
  invariantAlgebraEquiv (R := R) (A := NonzeroTorsionRing W n)
    (B := NonzeroTorsionRing V n) (G := (ZMod n)ˣ)
    (nonzeroTorsionCoordinateTransport (V := V) (W := W) n e)
    (nonzeroTorsionCoordinateTransport_equivariant (V := V) (W := W) n e he)

/-- The scalar quotient scheme is invariant under equivariant isomorphisms of generators. -/
def scalarQuotientTransportIso
    (e : nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n)
    (he : ∀ a : (ZMod n)ˣ, (nonzeroTorsionScalarAction V n a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction W n a).inv) :
    scalarQuotientModel V n ≅ scalarQuotientModel W n :=
  (algSpec (.of R)).mapIso (CommAlgCat.isoMk (scalarInvariantTransport (V := V) (W := W) n e he)).op


theorem nonzeroTorsionCoordinateTransport_spec
    (e : nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n) :
    (algSpec (.of R)).map (CommAlgCat.ofHom
      (nonzeroTorsionCoordinateTransport (V := V) (W := W) n e).toAlgHom).op =
      (nonzeroTorsionCoordinatePresentation V n).inv ≫ e.hom ≫
        (nonzeroTorsionCoordinatePresentation W n).hom := by
  change (algSpec (.of R)).map ((algSpec.fullyFaithful (R := .of R)).preimage
    ((nonzeroTorsionCoordinatePresentation V n).inv ≫ e.hom ≫
      (nonzeroTorsionCoordinatePresentation W n).hom)) = _
  exact (algSpec.fullyFaithful (R := .of R)).map_preimage _

/-- The quotient map is induced by inclusion of the invariant coordinates. -/
theorem scalarQuotientMap_presentation (W : WeierstrassCurve R) [W.IsElliptic] :
    scalarQuotientMap W n = (nonzeroTorsionCoordinatePresentation W n).hom ≫
      (algSpec (.of R)).map (CommAlgCat.ofHom (TorsionScalarInvariantRing W n).val).op := by
  apply Over.OverMorphism.ext
  rfl

theorem scalarQuotientTransportIso_hom
    (e : nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n)
    (he : ∀ a : (ZMod n)ˣ, (nonzeroTorsionScalarAction V n a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction W n a).inv) :
    (scalarQuotientTransportIso (V := V) (W := W) n e he).hom =
      (algSpec (.of R)).map (CommAlgCat.ofHom
        (scalarInvariantTransport (V := V) (W := W) n e he).toAlgHom).op := rfl

theorem scalarInvariantTransport_spec
    (e : nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n)
    (he : ∀ a : (ZMod n)ˣ, (nonzeroTorsionScalarAction V n a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction W n a).inv) :
    (algSpec (.of R)).map (CommAlgCat.ofHom
        (nonzeroTorsionCoordinateTransport (V := V) (W := W) n e).toAlgHom).op ≫
      (algSpec (.of R)).map (CommAlgCat.ofHom (TorsionScalarInvariantRing W n).val).op =
    (algSpec (.of R)).map (CommAlgCat.ofHom (TorsionScalarInvariantRing V n).val).op ≫
      (algSpec (.of R)).map (CommAlgCat.ofHom
        (scalarInvariantTransport (V := V) (W := W) n e he).toAlgHom).op := by
  have hr :
      (nonzeroTorsionCoordinateTransport (V := V) (W := W) n e).toAlgHom.comp
          (TorsionScalarInvariantRing W n).val =
        (TorsionScalarInvariantRing V n).val.comp
          (scalarInvariantTransport (V := V) (W := W) n e he).toAlgHom := by
    ext x
    rfl
  have hh := congrArg (fun f : TorsionScalarInvariantRing W n →ₐ[R] NonzeroTorsionRing V n =>
    (algSpec (.of R)).map (CommAlgCat.ofHom f).op) hr
  change (algSpec (.of R)).map
      ((CommAlgCat.ofHom
        (nonzeroTorsionCoordinateTransport (V := V) (W := W) n e).toAlgHom).op ≫
        (CommAlgCat.ofHom (TorsionScalarInvariantRing W n).val).op) =
    (algSpec (.of R)).map
      ((CommAlgCat.ofHom (TorsionScalarInvariantRing V n).val).op ≫
        (CommAlgCat.ofHom
          (scalarInvariantTransport (V := V) (W := W) n e he).toAlgHom).op) at hh
  simpa only [Functor.map_comp] using hh

private theorem conjugate_square {C : Type*} [Category C]
    {X Y A B P Q : C} (a : X ≅ A) (b : Y ≅ B)
    (f : X ⟶ Y) (i : A ⟶ P) (j : B ⟶ Q) (g : P ⟶ Q)
    (k : A ⟶ B) (hk : k = a.inv ≫ f ≫ b.hom)
    (h : k ≫ j = i ≫ g) :
    f ≫ (b.hom ≫ j) = (a.hom ≫ i) ≫ g := by
  subst k
  have hh := (Iso.inv_comp_eq a).mp
    ((Category.assoc a.inv (f ≫ b.hom) j).symm.trans h)
  simpa only [Category.assoc] using hh

attribute [local irreducible] nonzeroTorsionModel torsionModel
set_option backward.isDefEq.respectTransparency true in
/-- The induced cyclic-parameter isomorphism commutes with forgetting the generator. -/
theorem scalarQuotientTransportIso_quotient
    (e : nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n)
    (he : ∀ a : (ZMod n)ˣ, (nonzeroTorsionScalarAction V n a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction W n a).inv) :
    e.hom ≫ scalarQuotientMap W n =
      scalarQuotientMap V n ≫ (scalarQuotientTransportIso (V := V) (W := W) n e he).hom := by
  have h := conjugate_square (nonzeroTorsionCoordinatePresentation V n)
    (nonzeroTorsionCoordinatePresentation W n) e.hom
    ((algSpec (.of R)).map (CommAlgCat.ofHom (TorsionScalarInvariantRing V n).val).op)
    ((algSpec (.of R)).map (CommAlgCat.ofHom (TorsionScalarInvariantRing W n).val).op)
    ((algSpec (.of R)).map (CommAlgCat.ofHom
      (scalarInvariantTransport (V := V) (W := W) n e he).toAlgHom).op)
    ((algSpec (.of R)).map (CommAlgCat.ofHom
      (nonzeroTorsionCoordinateTransport (V := V) (W := W) n e).toAlgHom).op)
    (nonzeroTorsionCoordinateTransport_spec (V := V) (W := W) n e)
    (scalarInvariantTransport_spec (V := V) (W := W) n e he)
  rw [← scalarQuotientMap_presentation n V, ← scalarQuotientMap_presentation n W,
    ← scalarQuotientTransportIso_hom (V := V) (W := W) n e he] at h
  exact h


/-- Admissible coordinate changes identify the actual cyclic parameter schemes. -/
def variableChangeCyclicParameterIso (W : WeierstrassCurve R) [W.IsElliptic]
    (C : VariableChange R) :
    scalarQuotientModel (C • W) n ≅ scalarQuotientModel W n :=
  scalarQuotientTransportIso (V := C • W) (W := W) n
    (variableChangeNonzeroTorsionIso n W C)
    (variableChangeNonzeroTorsionIso_scalar n W C)

/-- Coordinate transport commutes with passage from a generator to its cyclic parameter. -/
theorem variableChangeCyclicParameterIso_quotient (W : WeierstrassCurve R) [W.IsElliptic]
    (C : VariableChange R) :
    (variableChangeNonzeroTorsionIso n W C).hom ≫ scalarQuotientMap W n =
      scalarQuotientMap (C • W) n ≫ (variableChangeCyclicParameterIso n W C).hom := by
  exact scalarQuotientTransportIso_quotient (V := C • W) (W := W) n
    (variableChangeNonzeroTorsionIso n W C)
    (variableChangeNonzeroTorsionIso_scalar n W C)

end WeierstrassCurve.CubicCharts
