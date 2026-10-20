/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TorusRootsOfUnitySubgroup

/-!
# Hopf coordinates for an arbitrary original toric finite subgroup

Affineness follows from the actual finite structure morphism. The affine group
scheme equivalence constructs its Hopf algebra and recovers the original group
inclusion in a specified torus coordinate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite MonObj

open scoped LaurentPolynomial

namespace FLT.Mazur.ToricFiniteSubgroupHopfPresentation

open GeneralizedEllipticCurve

variable {K : Type} [Field K] {E : GeneralizedEllipticCurve (Spec (.of K))}
  {n : ℕ} (H : E.FiniteSubgroup n)

/-- The original finite subgroup carrier is affine. -/
theorem carrier_affine : IsAffine H.carrier.left :=
  isAffine_of_isAffineHom H.carrier.hom

/-- The affine group equivalence applies to the original subgroup, without reducedness. -/
theorem in_hopf_image : (hopfSpec (.of K)).essImage (Grp.mk H.carrier) := by
  rw [essImage_hopfSpec]
  exact carrier_affine H

/-- The Hopf algebra constructed from the original affine group scheme. -/
def coordinates : CommHopfAlgCat K := (in_hopf_image H).witness.unop

/-- The constructed Hopf spectrum is the original subgroup as a group scheme. -/
def groupIso : (hopfSpec (.of K)).obj (op (coordinates H)) ≅ Grp.mk H.carrier :=
  (in_hopf_image H).getIso

/-- The same identification in the category over the original field. -/
def carrierIso : (Spec (.of (coordinates H))).asOver (Spec (.of K)) ≅ H.carrier :=
  (Grp.forget _).mapIso (groupIso H)

instance carrierIso_isMonHom : IsMonHom (carrierIso H).hom :=
  (groupIso H).hom.hom.isMonHom_hom

variable (e : MultiplicativeGroupScheme.gm K ≅ E.group) [IsMonHom e.hom]

/-- The original inclusion expressed in the specified torus coordinate. -/
def torusMap : H.carrier ⟶ MultiplicativeGroupScheme.gm K := H.inclusion ≫ e.inv

instance torusMap_isMonHom : IsMonHom (torusMap H e) := by
  unfold torusMap
  infer_instance

/-- The specified torus inclusion bundled as an actual group homomorphism. -/
def torusGroupMap : Grp.mk H.carrier ⟶ Grp.mk (MultiplicativeGroupScheme.gm K) :=
  Grp.ofHom (torusMap H e)

/-- Pull the actual toric group inclusion back through the fully faithful Hopf spectrum. -/
def restriction : K[T;T⁻¹] →ₐc[K] coordinates H :=
  ((hopfSpec.fullyFaithful (R := .of K)).preimage
    (X := op (coordinates H)) (Y := op (CommHopfAlgCat.of K K[T;T⁻¹]))
    ((groupIso H).hom ≫ torusGroupMap H e)).unop.hom

/-- Spectrum recovers precisely the original toric inclusion, with its original carrier. -/
theorem restriction_spec :
    Spec.map (CommRingCat.ofHom (restriction H e).toAlgHom.toRingHom) =
      (carrierIso H).hom.left ≫ (torusMap H e).left := by
  have h := (hopfSpec.fullyFaithful (R := .of K)).map_preimage
    (X := op (coordinates H)) (Y := op (CommHopfAlgCat.of K K[T;T⁻¹]))
    ((groupIso H).hom ≫ torusGroupMap H e)
  exact congrArg (fun g => g.hom.hom.left) h

/-- The affine coordinate comparison retains the original full curve inclusion. -/
theorem restriction_spec_curve :
    Spec.map (CommRingCat.ofHom (restriction H e).toAlgHom.toRingHom) ≫
      e.hom.left ≫ E.inclusion.left = (carrierIso H).hom.left ≫ H.curveMap.left := by
  rw [restriction_spec]
  simp [torusMap, FiniteSubgroup.curveMap, Category.assoc]

end FLT.Mazur.ToricFiniteSubgroupHopfPresentation
