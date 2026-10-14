/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSplitOrbitOpen

/-!
# Constructed monic seeds on actual affine split-orbit selections

Choose an affine neighborhood through a reflexive orbit point and restrict
the section to its open inverse image. This constructs, rather than assumes,
a two-sided etale seed monic over the new coefficient target. Under old
unramifiedness the selected affine source is open in the COMPLETE source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSplitOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (a : Z ⟶ A.left) (z : Z)
local notation "B" => (pullback q.left a : Scheme)
local notation "π" => pullback.snd q.left a

/-- The affine neighborhood is chosen through the constructed reflexive orbit point. -/
def affineSource : Scheme.{u} :=
  Spec ((B).affineOpenCover.X ((B).affineOpenCover.idx (sectionMap e a z)))

/-- Its actual affine open immersion into the original orbit. -/
def affineToOrbit : affineSource e a z ⟶ B :=
  (B).affineOpenCover.f ((B).affineOpenCover.idx (sectionMap e a z))

instance affineSource_isAffine : IsAffine (affineSource e a z) :=
  inferInstanceAs (IsAffine (Spec _))
instance affineToOrbit_isOpenImmersion : IsOpenImmersion (affineToOrbit e a z) :=
  inferInstanceAs (IsOpenImmersion ((B).affineOpenCover.f _))

/-- An actual open neighborhood of the requested new coefficient point. -/
def affineSeedOpen : Z.Opens := (sectionMap e a) ⁻¹ᵁ (affineToOrbit e a z).opensRange

/-- The chosen point really lies in the seed domain. -/
theorem mem_affineSeedOpen : z ∈ affineSeedOpen e a z :=
  (B).affineOpenCover.covers (sectionMap e a z)

/-- Restrict the section to construct a seed in the new affine source. -/
def affineSeed : (affineSeedOpen e a z).toScheme ⟶ affineSource e a z :=
  IsOpenImmersion.lift (affineToOrbit e a z)
    ((affineSeedOpen e a z).ι ≫ sectionMap e a) (by
      rintro _ ⟨x, rfl⟩
      exact x.property)

@[reassoc]
theorem affineSeed_toOrbit : affineSeed e a z ≫ affineToOrbit e a z =
    (affineSeedOpen e a z).ι ≫ sectionMap e a := IsOpenImmersion.lift_fac _ _ _

/-- The new target map is an open immersion, so its etaleness and monicity are constructed. -/
@[reassoc]
theorem affineSeed_target : affineSeed e a z ≫ (affineToOrbit e a z ≫ π) =
    (affineSeedOpen e a z).ι := by
  rw [← Category.assoc, affineSeed_toOrbit, Category.assoc,
    sectionMap_projection, Category.comp_id]

/-- The selected affine source remains etale over the new coefficient scheme. -/
theorem affineProjection_etale [Etale q.left] : Etale (affineToOrbit e a z ≫ π) :=
  inferInstance

/-- All geometric requirements on the initial monic seed are now proved. -/
theorem affineSeed_geometry [Etale q.left] :
    Etale (affineSeed e a z) ∧ Etale (affineSeed e a z ≫ (affineToOrbit e a z ≫ π)) ∧
      Mono (affineSeed e a z ≫ (affineToOrbit e a z ≫ π)) := by
  let _ := affineProjection_etale e a z
  let _ : IsOpenImmersion (affineSeed e a z ≫ (affineToOrbit e a z ≫ π)) := by
    rw [affineSeed_target]
    infer_instance
  exact ⟨Etale.of_comp _ (affineToOrbit e a z ≫ π), inferInstance, inferInstance⟩

/-- The constructed affine seed retains exactly the requested original source point. -/
theorem affineSeed_point :
    (affineToOrbit e a z ≫
      SchemeRelationEtaleBranchPropagation.branch p.left q.left a)
        (affineSeed e a z ⟨z, mem_affineSeedOpen e a z⟩) = a z := by
  have he : affineSeed e a z ≫ affineToOrbit e a z ≫
      SchemeRelationEtaleBranchPropagation.branch p.left q.left a =
        (affineSeedOpen e a z).ι ≫ a := by
    rw [affineSeed_toOrbit_assoc, sectionMap_source]
  exact congrArg (fun g ↦ g ⟨z, mem_affineSeedOpen e a z⟩) he

variable {T : Scheme.{u}} (w : A.left ⟶ T) (h : p.left ≫ w = q.left ≫ w)
  [Mono (pullback.lift p.left q.left h)] [Etale p.left] [Etale a]
  [FormallyUnramified w] [LocallyOfFiniteType w]

/-- These are genuine affine open selections of the entire changed source, not reduced strata. -/
theorem affineSource_isOpenImmersion :
    IsOpenImmersion (affineToOrbit e a z ≫ inclusion w h a) := by
  let _ := inclusion_isOpenImmersion w h a
  infer_instance

end FLT.Mazur.SchemeRelationSplitOrbit
