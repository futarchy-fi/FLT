/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationEtaleSourceFunctions
public import FLT.Mazur.InvariantOpenRelationFunctions

/-!
# Etale charts over their actual original orbit images

An etale source factors through the source open of its orbit image. If its
image is invariant under the full relation, this factorization is surjective.
The map on functions is the existing original invariant descent comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  {T : Scheme.{0}} (j : T ⟶ A.left) [Etale j]
local notation "O" => orbitImageOpen e hq (etaleSourceImage j)
set_option quotPrecheck false
local notation "E" => (pullOpen e O).val

/-- The original etale chart factors through the entire source of its orbit image. -/
def etaleOrbitImageMap : T ⟶ (E).toScheme :=
  IsOpenImmersion.lift (E).ι j (by
    rw [Scheme.Opens.range_ι]
    exact le_saturateOpen e hq (etaleSourceImage j))

/-- The factorization retains the unchanged original chart morphism. -/
@[reassoc] theorem etaleOrbitImageMap_ι : etaleOrbitImageMap e hq j ≫ (E).ι = j :=
  IsOpenImmersion.lift_fac _ _ _

instance etaleOrbitImageMap_etale : Etale (etaleOrbitImageMap e hq j) := by
  let _ : Etale (etaleOrbitImageMap e hq j ≫ (E).ι) := by
    rw [etaleOrbitImageMap_ι]
    infer_instance
  exact Etale.of_comp _ (E).ι

/-- A full-relation invariant image is already the whole pulled-back orbit domain. -/
theorem etaleOrbitImage_source_eq
    (hi : p.left ⁻¹ᵁ etaleSourceImage j = q.left ⁻¹ᵁ etaleSourceImage j) :
    E = etaleSourceImage j :=
  congrArg Subtype.val (saturateOpen_of_invariant e hq ⟨etaleSourceImage j, hi⟩)

/-- Saturation makes this actual etale chart a cover of the original orbit source. -/
theorem etaleOrbitImageMap_surjective
    (hi : p.left ⁻¹ᵁ etaleSourceImage j = q.left ⁻¹ᵁ etaleSourceImage j) :
    Surjective (etaleOrbitImageMap e hq j) where
  surj x := by
    have hx : x.val ∈ etaleSourceImage j :=
      (etaleOrbitImage_source_eq e hq j hi).le x.property
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, Subtype.ext ?_⟩
    exact (congrArg (fun g ↦ g y) (etaleOrbitImageMap_ι e hq j)).trans hy

variable [Etale q.left]

/-- Orbit descent is precisely pullback along the geometric source factorization. -/
theorem etaleOrbitImageMap_appTop (b : (invariantSheaf e).obj.obj (op O)) :
    (etaleOrbitImageMap e hq j).appTop (orbitFunctions e O b).val =
      (etaleSourceFunctionEquiv e hq j b).val := by
  rw [etaleSourceFunctionEquiv_appLE e hq j b
    (show ⊤ ≤ j ⁻¹ᵁ E from fun x _ ↦ le_saturateOpen e hq _ ⟨x, rfl⟩)]
  change (etaleOrbitImageMap e hq j).appTop
    ((E).topIso.inv ((invariantInclusion e).hom.app (op O) b)) = _
  have ht : (E).topIso.inv = (E).ι.appLE E ⊤ (E).ι_preimage_self.ge := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    congr 1
  rw [ht]
  have hc := Scheme.Hom.appLE_comp_appLE (etaleOrbitImageMap e hq j) (E).ι
    E ⊤ ⊤ (E).ι_preimage_self.ge le_rfl
  have he : (etaleOrbitImageMap e hq j).appLE ⊤ ⊤ le_rfl =
      (etaleOrbitImageMap e hq j).appTop := by simp [Scheme.Hom.appLE]
  simp only [etaleOrbitImageMap_ι, he] at hc
  exact congrArg (fun g ↦ g ((invariantInclusion e).hom.app (op O) b)) hc

end FLT.Mazur.RelativeRelationOrbit
