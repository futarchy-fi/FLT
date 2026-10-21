/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicInitialCoefficientTransport
public import FLT.Mazur.OneGonAdicCharacterCoefficientTower

/-!
# The coefficient comparison retains the specified initial roots

The actual boundary-root map, including its corrected torus coordinate and
parameter equality transport, is preserved by every map of coefficient pairs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open OneGonSmoothing WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The native boundary square retains arbitrary zero-parameter equality transports. -/
@[reassoc] theorem boundaryRootsHom_parameter_projection {A B : Type}
    [CommRing A] [CommRing B] (f : A →+* B) (a : A) (b : B)
    (ha : a = 0) (hb : b = 0) (h : equation b = (equation a).map f)
    (n : ℕ) [NeZero n] :
    ((boundaryRootsHom (R := B) n).hom.hom.hom.left ≫
      eqToHom (congrArg (fun U => (integralSmoothOpen U).toScheme)
        (congrArg equation hb.symm))) ≫ smoothCoefficientMapTo _ _ f h =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (ZMod n) f)) ≫
        (boundaryRootsHom (R := A) n).hom.hom.hom.left ≫
          eqToHom (congrArg (fun U => (integralSmoothOpen U).toScheme)
            (congrArg equation ha.symm)) := by
  subst a
  subst b
  simp only [eqToHom_refl, Category.comp_id]
  exact boundaryRootsHom_ring_projection f n h

/-- The underlying scheme map preserves abstract commutative-group composition. -/
theorem commGrp_comp_left {S : Scheme} {G H K : CommGrp (Over S)}
    (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g).hom.hom.hom.left = f.hom.hom.hom.left ≫ g.hom.hom.hom.left := rfl

/-- Projection of the initial homomorphism retains its two specified factors. -/
theorem initialRootsHom_left {A : Type} [CommRing A]
    (K : Ideal A) (a : A) (ha : a ∈ K) (n : ℕ) [NeZero n] :
    (initialRootsHom n K a ha).hom.hom.hom.left =
      (boundaryRootsHom (R := StageRing K 0) n).hom.hom.hom.left ≫
        (initialBoundaryIso K a ha).hom.hom.hom.hom.left :=
  commGrp_comp_left (boundaryRootsHom (R := StageRing K 0) n) (initialBoundaryIso K a ha).hom

variable {R S : Type} [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f)
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

attribute [local irreducible] boundaryRootsHom

/-- The native initial roots maps form the actual coefficient square. -/
@[reassoc] theorem initialRootsHom_coefficient_projection :
    (initialRootsHom n J (f t) (hf ht)).hom.hom.hom.left ≫
      stageSmoothCoefficient I J f hf t 0 =
        Spec.map (CommRingCat.ofHom (stageCharacterCoefficient I J f hf 0)) ≫
          (initialRootsHom n I t ht).hom.hom.hom.left := by
  rw [initialRootsHom_left J (f t) (hf ht) n, initialRootsHom_left I t ht n,
    initialBoundaryIso_hom_left J (f t) (hf ht), initialBoundaryIso_hom_left I t ht]
  exact boundaryRootsHom_parameter_projection (stageCoefficient I J f hf 0)
    (parameter I t 0) (parameter J (f t) 0) (parameter_zero I t ht)
    (parameter_zero J (f t) (hf ht)) (stageCoefficient_equation I J f hf t 0) n


/-- The changed initial tower map is exactly the independently specified initial roots. -/
theorem coefficientTower_initialRoots :
    coefficientTower I J f hf t ht (initialRootsHom n I t ht) 0 =
      initialRootsHom n J (f t) (hf ht) := by
  rw [coefficientTower, tower_zero]
  symm
  apply characterCoefficientHom_unique
  exact initialRootsHom_coefficient_projection I J f hf t ht n

/-- Every finite-order map retains the independently specified canonical initial roots. -/
theorem canonicalTower_coefficient :
    coefficientTower I J f hf t ht (initialRootsHom n I t ht) =
      tower J (f t) (hf ht) (initialRootsHom n J (f t) (hf ht)) := by
  rw [coefficientTower_eq, coefficientTower_initialRoots]

/-- The canonical finite towers retain the entire coefficient square at every order. -/
@[reassoc] theorem canonicalTower_coefficient_projection (m : ℕ) :
    (tower J (f t) (hf ht) (initialRootsHom n J (f t) (hf ht)) m).hom.hom.hom.left ≫
      stageSmoothCoefficient I J f hf t m =
        Spec.map (CommRingCat.ofHom (stageCharacterCoefficient I J f hf m)) ≫
          (tower I t ht (initialRootsHom n I t ht) m).hom.hom.hom.left := by
  rw [← canonicalTower_coefficient I J f hf t ht n]
  exact coefficientTower_projection I J f hf t ht (initialRootsHom n I t ht) m

end FLT.Mazur.OneGonAdicCharacterTower
