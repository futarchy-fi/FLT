/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionScalars
public import Mathlib.RingTheory.Invariant.Basic
/-! # The affine quotient of nonzero torsion by scalar units

The spectrum of the coordinate invariants is constructed from the actual
scheme action. It is finite over the coefficient base, and the quotient map
is finite and surjective. Prime-level cyclic-subgroup interpretation and
étaleness of this quotient are separate from these assertions.
-/

open AlgebraicGeometry CategoryTheory Opposite
open scoped Pointwise
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- Contravariance and inversion turn opposite algebra automorphisms into algebra automorphisms. -/
def unopCoordinateAut (A : CommAlgCat R) : Aut (op A) →* (A ≃ₐ[R] A) where
  toFun e := CommAlgCat.algEquivOfIso e.symm.unop
  map_one' := by ext x; rfl
  map_mul' e f := by ext x; rfl

/-- Affine scheme automorphisms act on coordinates by inverse pullback. -/
def affineCoordinateAut (A : Type u) [CommRing A] [Algebra R A]
    (X : Over (Spec (.of R)))
    (e : X ≅ (algSpec (.of R)).obj (op (CommAlgCat.of R A))) :
    Aut X →* (A ≃ₐ[R] A) :=
  (unopCoordinateAut (CommAlgCat.of R A)).comp
    (((algSpec.fullyFaithful (R := .of R)).autMulEquivOfFullyFaithful
      (op (CommAlgCat.of R A))).symm.toMonoidHom.comp
      (Aut.autMulEquivOfIso e).toMonoidHom)


/-- The coordinate automorphism pulls back along the inverse scheme automorphism. -/
theorem affineCoordinateAut_spec (A : Type u) [CommRing A] [Algebra R A]
    (X : Over (Spec (.of R)))
    (e : X ≅ (algSpec (.of R)).obj (op (CommAlgCat.of R A))) (σ : Aut X) :
    (algSpec (.of R)).map
      (CommAlgCat.ofHom (affineCoordinateAut A X e σ).toAlgHom).op =
        e.inv ≫ σ.inv ≫ e.hom := by
  change (algSpec (.of R)).map ((algSpec.fullyFaithful (R := .of R)).preimage
    (e.inv ≫ σ.inv ≫ e.hom)) = _
  exact (algSpec.fullyFaithful (R := .of R)).map_preimage _

variable [IsNoetherianRing R] [IsDomain R] (W : WeierstrassCurve R) [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

instance nonzeroTorsionFinite : IsFinite (nonzeroTorsionModel W n).hom :=
  nonzeroTorsionModel_finite W n Fact.out

instance nonzeroTorsionAffine : IsAffine (nonzeroTorsionModel W n).left :=
  isAffine_of_isAffineHom (nonzeroTorsionModel W n).hom

/-- The actual global-section ring of the nonzero torsion parameter scheme. -/
abbrev NonzeroTorsionRing : Type u := Γ((nonzeroTorsionModel W n).left, ⊤)

instance nonzeroTorsionAlgebra : Algebra R (NonzeroTorsionRing W n) :=
  instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfOverSpecOfIsAffine
    (R := .of R) (X := (nonzeroTorsionModel W n).left)

/-- The nonzero torsion coordinate ring is finite over the base. -/
theorem nonzeroTorsionRing_finite : Module.Finite R (NonzeroTorsionRing W n) := by
  apply RingHom.finite_algebraMap.mp
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom
    (algebraMap R (NonzeroTorsionRing W n)))).mp
  change IsFinite (Scheme.Spec.map (Spec.fullyFaithful.preimage
    ((nonzeroTorsionModel W n).left.isoSpec.inv ≫ (nonzeroTorsionModel W n).hom)))
  rw [Spec.fullyFaithful.map_preimage]
  infer_instance

/-- The actual generator-changing action on the coordinate algebra. -/
def nonzeroTorsionRingScalar : (ZMod n)ˣ →* (NonzeroTorsionRing W n ≃ₐ[R]
    NonzeroTorsionRing W n) := by
  let e : nonzeroTorsionModel W n ≅
      (algSpec (.of R)).obj (op (CommAlgCat.of R (NonzeroTorsionRing W n))) :=
    (nonzeroTorsionModel W n).left.isoSpec.asOver (Spec (.of R))
  let f : Aut (nonzeroTorsionModel W n) →*
      (NonzeroTorsionRing W n ≃ₐ[R] NonzeroTorsionRing W n) :=
    affineCoordinateAut (NonzeroTorsionRing W n) (nonzeroTorsionModel W n) e
  exact f.comp (nonzeroTorsionScalarAction W n)

instance nonzeroTorsionRingAction :
    MulSemiringAction (ZMod n)ˣ (NonzeroTorsionRing W n) :=
  MulSemiringAction.compHom _ (nonzeroTorsionRingScalar W n)

instance nonzeroTorsionRingActionComm :
    SMulCommClass (ZMod n)ˣ R (NonzeroTorsionRing W n) where
  smul_comm g r x := (nonzeroTorsionRingScalar W n g).toLinearEquiv.map_smul r x

/-- The subalgebra of coordinates fixed by all scalar units. -/
abbrev TorsionScalarInvariantRing :=
  FixedPoints.subalgebra R (NonzeroTorsionRing W n) (ZMod n)ˣ

/-- The invariant coordinate ring is finite over the noetherian base. -/
theorem torsionScalarInvariantRing_finite : Module.Finite R (TorsionScalarInvariantRing W n) := by
  have := nonzeroTorsionRing_finite W n
  exact Module.Finite.of_injective (TorsionScalarInvariantRing W n).val.toLinearMap
    Subtype.val_injective

/-- The affine scheme defined by the scalar-invariant coordinate algebra. -/
def scalarQuotientModel : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TorsionScalarInvariantRing W n))))

/-- The scalar quotient is finite over the coefficient base. -/
theorem scalarQuotientModel_finite : IsFinite (scalarQuotientModel W n).hom := by
  have := torsionScalarInvariantRing_finite W n
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (TorsionScalarInvariantRing W n))))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The nonzero torsion coordinate ring is finite over its scalar invariants. -/
theorem nonzeroTorsionRing_finite_invariants :
    Module.Finite (TorsionScalarInvariantRing W n) (NonzeroTorsionRing W n) := by
  have := nonzeroTorsionRing_finite W n
  exact Module.Finite.of_restrictScalars_finite R _ _

/-- The actual affine map from nonzero torsion to the spectrum of its invariants. -/
def scalarQuotientMap : nonzeroTorsionModel W n ⟶ scalarQuotientModel W n :=
  ((nonzeroTorsionModel W n).left.isoSpec.asOver (Spec (.of R))).hom ≫
    (Spec.map (CommRingCat.ofHom
      (TorsionScalarInvariantRing W n).val.toRingHom)).asOver (Spec (.of R))

/-- The map to the scalar quotient is finite. -/
theorem scalarQuotientMap_finite : IsFinite (scalarQuotientMap W n).left := by
  have := nonzeroTorsionRing_finite_invariants W n
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (TorsionScalarInvariantRing W n).val.toRingHom)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  change IsFinite ((nonzeroTorsionModel W n).left.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (TorsionScalarInvariantRing W n).val.toRingHom))
  infer_instance

/-- Every point of the scalar quotient is covered by a nonzero torsion point. -/
theorem scalarQuotientMap_surjective : Surjective (scalarQuotientMap W n).left := by
  have := nonzeroTorsionRing_finite_invariants W n
  have : Algebra.IsIntegral (TorsionScalarInvariantRing W n) (NonzeroTorsionRing W n) :=
    Algebra.IsIntegral.of_finite _ _
  have : Surjective (Spec.map (CommRingCat.ofHom
      (TorsionScalarInvariantRing W n).val.toRingHom)) :=
    ⟨Algebra.IsIntegral.comap_surjective _ _⟩
  change Surjective ((nonzeroTorsionModel W n).left.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (TorsionScalarInvariantRing W n).val.toRingHom))
  infer_instance

instance scalarInvariantExtension :
    Algebra.IsInvariant (TorsionScalarInvariantRing W n) (NonzeroTorsionRing W n) (ZMod n)ˣ where
  isInvariant x hx := ⟨⟨x, hx⟩, rfl⟩

/-- Primes above the same invariant prime lie in one scalar orbit. -/
theorem scalarInvariantPrime_orbit
    (P Q : Ideal (NonzeroTorsionRing W n)) [P.IsPrime] [Q.IsPrime]
    (h : P.under (TorsionScalarInvariantRing W n) = Q.under (TorsionScalarInvariantRing W n)) :
    ∃ g : (ZMod n)ˣ, Q = g • P := by
  exact Algebra.IsInvariant.exists_smul_of_under_eq
    (TorsionScalarInvariantRing W n) (NonzeroTorsionRing W n) (ZMod n)ˣ P Q h


/-- An invariant algebra map factors through the scalar invariants. -/
def scalarInvariantLift (B : Type u) [CommRing B] [Algebra R B]
    (f : B →ₐ[R] NonzeroTorsionRing W n)
    (hf : ∀ (g : (ZMod n)ˣ) b, g • f b = f b) :
    B →ₐ[R] TorsionScalarInvariantRing W n :=
  f.codRestrict _ (fun b g => hf g b)

/-- The invariant factorization recovers the original algebra map. -/
theorem scalarInvariantLift_fac (B : Type u) [CommRing B] [Algebra R B]
    (f : B →ₐ[R] NonzeroTorsionRing W n)
    (hf : ∀ (g : (ZMod n)ˣ) b, g • f b = f b) :
    (TorsionScalarInvariantRing W n).val.comp (scalarInvariantLift W n B f hf) = f := rfl

/-- The factorization through coordinate invariants is unique. -/
theorem scalarInvariantLift_unique (B : Type u) [CommRing B] [Algebra R B]
    (f : B →ₐ[R] NonzeroTorsionRing W n)
    (hf : ∀ (g : (ZMod n)ˣ) b, g • f b = f b)
    (j : B →ₐ[R] TorsionScalarInvariantRing W n)
    (hj : (TorsionScalarInvariantRing W n).val.comp j = f) :
    j = scalarInvariantLift W n B f hf := by
  ext b
  exact AlgHom.congr_fun hj b


/-- The quotient map is unchanged by the inverse scalar action. -/
theorem scalarQuotientMap_invariant_inv (g : (ZMod n)ˣ) :
    (nonzeroTorsionScalarAction W n g).inv ≫ scalarQuotientMap W n =
      scalarQuotientMap W n := by
  let A := NonzeroTorsionRing W n
  let D := TorsionScalarInvariantRing W n
  let e : nonzeroTorsionModel W n ≅
      (algSpec (.of R)).obj (op (CommAlgCat.of R A)) :=
    (nonzeroTorsionModel W n).left.isoSpec.asOver (Spec (.of R))
  let i : D →ₐ[R] A := (TorsionScalarInvariantRing W n).val
  let a : A ≃ₐ[R] A := nonzeroTorsionRingScalar W n g
  have hi : a.toAlgHom.comp i = i := by
    ext x
    exact x.property g
  have hs : (algSpec (.of R)).map (CommAlgCat.ofHom a.toAlgHom).op ≫
      (algSpec (.of R)).map (CommAlgCat.ofHom i).op =
        (algSpec (.of R)).map (CommAlgCat.ofHom i).op := by
    rw [← Functor.map_comp]
    congr 1
    exact congrArg (fun f : D →ₐ[R] A => (CommAlgCat.ofHom f).op) hi
  have ha : (algSpec (.of R)).map (CommAlgCat.ofHom a.toAlgHom).op =
      e.inv ≫ (nonzeroTorsionScalarAction W n g).inv ≫ e.hom :=
    affineCoordinateAut_spec A (nonzeroTorsionModel W n) e
      (nonzeroTorsionScalarAction W n g)
  rw [ha] at hs
  have h := congrArg (fun f => e.hom ≫ f) hs
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  apply Over.OverMorphism.ext
  exact congrArg Over.Hom.left h

/-- The quotient map is unchanged by every scalar change of generator. -/
theorem scalarQuotientMap_invariant (g : (ZMod n)ˣ) :
    (nonzeroTorsionScalarAction W n g).hom ≫ scalarQuotientMap W n =
      scalarQuotientMap W n := by
  have h := congrArg (fun f => (nonzeroTorsionScalarAction W n g).hom ≫ f)
    (scalarQuotientMap_invariant_inv W n g)
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h.symm

end WeierstrassCurve.CubicCharts
