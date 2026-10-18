/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantAffineCover
public import FLT.Mazur.FiniteNeighborhoodQuotientCover

/-!
# The actual normalized characteristic quotients

Glue the invariant-coordinate quotients of the already constructed normalized
parameter loci. The original relabeling actions give integral surjective
quotient maps and their universal properties for arbitrary scheme targets.
Finite type of the original loci then makes these quotient maps finite.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The quotient of the actual normalized locus by its original relabeling group. -/
def normalizedQuotient : Scheme := StableAffineQuotient.glued (normalizedRelabelAction n b)

/-- The constructed quotient map on the original normalized parameter scheme. -/
def normalizedQuotientMap : normalizedLocus n b ⟶ normalizedQuotient n b :=
  FiniteGroupNeighborhoodCover.quotientMap (normalizedRelabelAction n b)
    (normalizedLocus_hasFiniteNeighborhoods n b)

/-- The original relabeling action leaves the quotient map invariant. -/
@[reassoc] theorem normalizedQuotientMap_invariant (g : RelabelGroup n) :
    (normalizedRelabelAction n b g).hom ≫ normalizedQuotientMap n b =
      normalizedQuotientMap n b :=
  FiniteGroupNeighborhoodCover.quotientMap_invariant _ _ g

/-- The actual normalized quotient map is integral. -/
instance normalizedQuotientMap_integral : IsIntegralHom (normalizedQuotientMap n b) := by
  unfold normalizedQuotientMap
  infer_instance

/-- Every point of the actual quotient has an original normalized parameter representative. -/
instance normalizedQuotientMap_surjective : Surjective (normalizedQuotientMap n b) := by
  unfold normalizedQuotientMap
  infer_instance

/-- The quotient point fibers identify exactly the original relabeling orbits. -/
theorem normalizedQuotientMap_eq_iff_orbit (x y : normalizedLocus n b) :
    normalizedQuotientMap n b x = normalizedQuotientMap n b y ↔
      ∃ g : RelabelGroup n, y = (normalizedRelabelAction n b g).hom x :=
  FiniteGroupNeighborhoodCover.quotientMap_eq_iff_orbit _ _ x y

/-- Invariant maps from the original normalized locus descend uniquely to any scheme. -/
theorem normalizedQuotientMap_existsUnique_desc {Y : Scheme} (f : normalizedLocus n b ⟶ Y)
    (hf : ∀ g : RelabelGroup n, (normalizedRelabelAction n b g).hom ≫ f = f) :
    ∃! k : normalizedQuotient n b ⟶ Y, normalizedQuotientMap n b ≫ k = f :=
  FiniteGroupNeighborhoodCover.quotientMap_existsUnique_desc _ _ f hf

/-- The integer structure morphism of the actual quotient scheme. -/
def normalizedQuotientToInt : normalizedQuotient n b ⟶ Spec (.of ℤ) :=
  specZIsTerminal.from _

/-- The quotient map preserves the original integer structure morphism. -/
@[reassoc] theorem normalizedQuotientMap_toInt :
    normalizedQuotientMap n b ≫ normalizedQuotientToInt n b = normalizedLocusToInt n b :=
  specZIsTerminal.hom_ext _ _

/-- Finite type of the original parameter locus implies finite type of its quotient map. -/
instance normalizedQuotientMap_locallyOfFiniteType :
    LocallyOfFiniteType (normalizedQuotientMap n b) := by
  have : LocallyOfFiniteType
      (normalizedQuotientMap n b ≫ normalizedQuotientToInt n b) := by
    rw [normalizedQuotientMap_toInt]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (normalizedQuotientToInt n b)

/-- The actual normalized relabeling quotient map is finite. -/
instance normalizedQuotientMap_finite : IsFinite (normalizedQuotientMap n b) :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

/-- The finite quotient map is proper, without asserting properness over the integers. -/
instance normalizedQuotientMap_proper : IsProper (normalizedQuotientMap n b) := inferInstance

/-- The quotient topology is the actual quotient topology of the normalized parameter locus. -/
theorem normalizedQuotientMap_isQuotientMap : Topology.IsQuotientMap (normalizedQuotientMap n b) :=
  (normalizedQuotientMap n b).isClosedMap.isQuotientMap
    (normalizedQuotientMap n b).continuous (normalizedQuotientMap n b).surjective

end FLT.Mazur.CyclicCharacteristicAtlas
