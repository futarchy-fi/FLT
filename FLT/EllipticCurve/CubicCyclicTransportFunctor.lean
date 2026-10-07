/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicParameterTransport
public import FLT.EllipticCurve.CubicCyclicEtale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Composition of cyclic parameter transport

The prime-level generator map is an effective epimorphism of schemes.
Cancellation by this cover proves the identity and composition laws for
transport of cyclic parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable {U V W : WeierstrassCurve R} [U.IsElliptic] [V.IsElliptic] [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]

/-- The finite étale surjection forgetting a prime generator is an effective epimorphism. -/
instance scalarQuotientMapEffectiveEpi (W : WeierstrassCurve R) [W.IsElliptic] :
    EffectiveEpi (scalarQuotientMap W p).left := by
  have := scalarQuotientMap_finite W p
  have := scalarQuotientMap_etale W p
  have := scalarQuotientMap_surjective W p
  infer_instance

/-- Forgetting a prime generator is epimorphic over the coefficient base. -/
instance scalarQuotientMapEpi (W : WeierstrassCurve R) [W.IsElliptic] :
    Epi (scalarQuotientMap W p) :=
  Over.epi_of_epi_left _

attribute [local irreducible] nonzeroTorsionModel torsionModel

omit [Fact (IsUnit (p : R))] in
/-- The identity isomorphism intertwines scalar actions. -/
theorem scalarTransport_refl_equivariant (W : WeierstrassCurve R) [W.IsElliptic]
    (a : (ZMod p)ˣ) :
    (nonzeroTorsionScalarAction W p a).inv ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (nonzeroTorsionScalarAction W p a).inv := by
  simp

omit [Fact (IsUnit (p : R))] in
/-- Equivariant isomorphisms compose. -/
theorem scalarTransport_trans_equivariant
    (e : nonzeroTorsionModel U p ≅ nonzeroTorsionModel V p)
    (f : nonzeroTorsionModel V p ≅ nonzeroTorsionModel W p)
    (he : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction U p a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction V p a).inv)
    (hf : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction V p a).inv ≫ f.hom =
      f.hom ≫ (nonzeroTorsionScalarAction W p a).inv)
    (a : (ZMod p)ˣ) :
    (nonzeroTorsionScalarAction U p a).inv ≫ (e.trans f).hom =
      (e.trans f).hom ≫ (nonzeroTorsionScalarAction W p a).inv := by
  simp only [Iso.trans_hom]
  rw [← Category.assoc, he, Category.assoc, hf, Category.assoc]

/-- Identity transport induces the identity on cyclic parameters. -/
theorem scalarQuotientTransportIso_refl (W : WeierstrassCurve R) [W.IsElliptic] :
    scalarQuotientTransportIso (V := W) (W := W) p (Iso.refl _)
      (scalarTransport_refl_equivariant p W) = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_epi (scalarQuotientMap W p)).mp
  rw [← scalarQuotientTransportIso_quotient]
  simp

/-- Transport of cyclic parameters respects composition. -/
theorem scalarQuotientTransportIso_trans
    (e : nonzeroTorsionModel U p ≅ nonzeroTorsionModel V p)
    (f : nonzeroTorsionModel V p ≅ nonzeroTorsionModel W p)
    (he : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction U p a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction V p a).inv)
    (hf : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction V p a).inv ≫ f.hom =
      f.hom ≫ (nonzeroTorsionScalarAction W p a).inv) :
    scalarQuotientTransportIso (V := U) (W := W) p (e.trans f)
        (scalarTransport_trans_equivariant p e f he hf) =
      (scalarQuotientTransportIso (V := U) (W := V) p e he).trans
        (scalarQuotientTransportIso (V := V) (W := W) p f hf) := by
  apply Iso.ext
  apply (cancel_epi (scalarQuotientMap U p)).mp
  simp only [Iso.trans_hom]
  rw [← scalarQuotientTransportIso_quotient, ← Category.assoc,
    ← scalarQuotientTransportIso_quotient, Category.assoc,
    ← scalarQuotientTransportIso_quotient]
  simp only [Iso.trans_hom, Category.assoc]

omit [Fact (IsUnit (p : R))] in
/-- Scalar automorphisms commute with every inverse scalar action. -/
theorem scalarTransport_scalar_equivariant (W : WeierstrassCurve R) [W.IsElliptic]
    (a b : (ZMod p)ˣ) :
    (nonzeroTorsionScalarAction W p b).inv ≫ (nonzeroTorsionScalarAction W p a).hom =
      (nonzeroTorsionScalarAction W p a).hom ≫ (nonzeroTorsionScalarAction W p b).inv := by
  have h := congrArg (nonzeroTorsionScalarAction W p) (mul_comm a b⁻¹)
  simpa only [map_mul, map_inv, Aut.Aut_mul_def, Aut.Aut_inv_def, Iso.trans_hom,
    Iso.symm_hom] using
    congrArg Iso.hom h

/-- Multiplying generators by a unit induces the identity on cyclic parameters. -/
theorem scalarQuotientTransportIso_scalar (W : WeierstrassCurve R) [W.IsElliptic]
    (a : (ZMod p)ˣ) :
    scalarQuotientTransportIso (V := W) (W := W) p (nonzeroTorsionScalarAction W p a)
      (scalarTransport_scalar_equivariant p W a) = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_epi (scalarQuotientMap W p)).mp
  rw [← scalarQuotientTransportIso_quotient, scalarQuotientMap_invariant]
  simp

/-- Transport maps differing by a scalar induce the same cyclic-parameter isomorphism. -/
theorem scalarQuotientTransportIso_eq_of_scalar
    (e f : nonzeroTorsionModel V p ≅ nonzeroTorsionModel W p)
    (he : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction V p a).inv ≫ e.hom =
      e.hom ≫ (nonzeroTorsionScalarAction W p a).inv)
    (hf : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction V p a).inv ≫ f.hom =
      f.hom ≫ (nonzeroTorsionScalarAction W p a).inv)
    (a : (ZMod p)ˣ) (h : f.hom = e.hom ≫ (nonzeroTorsionScalarAction W p a).hom) :
    scalarQuotientTransportIso (V := V) (W := W) p e he =
      scalarQuotientTransportIso (V := V) (W := W) p f hf := by
  apply Iso.ext
  apply (cancel_epi (scalarQuotientMap V p)).mp
  rw [← scalarQuotientTransportIso_quotient, ← scalarQuotientTransportIso_quotient,
    h, Category.assoc, scalarQuotientMap_invariant]


end WeierstrassCurve.CubicCharts
