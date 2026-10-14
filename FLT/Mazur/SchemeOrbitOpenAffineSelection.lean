/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOrbitOpenSelectionKernel

/-!
# Affine open parameter charts through the retained original seeds

An eligible reflexive seed gives an actual affine open in the parameter
scheme and a monic etale seed. The old orbit and new ground coordinates
remain literal scheme maps. No eligibility or global coverage is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOrbitOpenSelection
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S Z H : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (a : Z ⟶ A.left)
  (j : pullback q.left a ⟶ H) [Mono j] [Etale q.left]
  (z : (seedOpen e a j).toScheme)
local notation "U" => parameterOpen a j
local notation "x" => seed e a j z

/-- A constructed affine open neighborhood through the retained reflexive parameter point. -/
def affineSource : Scheme :=
  Spec ((U).toScheme.affineOpenCover.X ((U).toScheme.affineOpenCover.idx x))

/-- The actual affine open map into the selected parameters. -/
def affineToOpen : affineSource e a j z ⟶ (U).toScheme :=
  (U).toScheme.affineOpenCover.f ((U).toScheme.affineOpenCover.idx x)

instance affineSource_isAffine : IsAffine (affineSource e a j z) :=
  inferInstanceAs (IsAffine (Spec _))
instance affineToOpen_isOpenImmersion : IsOpenImmersion (affineToOpen e a j z) :=
  inferInstanceAs (IsOpenImmersion
    ((U).toScheme.affineOpenCover.f ((U).toScheme.affineOpenCover.idx x)))

/-- The chart is open in the actual parameter scheme, not only in the coefficient source. -/
def affineChart : affineSource e a j z ⟶ H := affineToOpen e a j z ≫ (U).ι

instance affineChart_isOpenImmersion : IsOpenImmersion (affineChart e a j z) :=
  inferInstanceAs (IsOpenImmersion (affineToOpen e a j z ≫ (U).ι))

/-- The new seed domain is an actual open neighborhood of the requested seed. -/
def affineSeedDomain : (seedOpen e a j).toScheme.Opens :=
  seed e a j ⁻¹ᵁ (affineToOpen e a j z).opensRange

omit [Mono j] [Etale q.left] in
/-- The selected neighborhood contains the requested original seed. -/
theorem mem_affineSeedDomain : z ∈ affineSeedDomain e a j z :=
  (U).toScheme.affineOpenCover.covers x

/-- Restrict the constructed section to the selected affine parameter neighborhood. -/
def affineSeed : (affineSeedDomain e a j z).toScheme ⟶ affineSource e a j z :=
  IsOpenImmersion.lift (affineToOpen e a j z)
    ((affineSeedDomain e a j z).ι ≫ seed e a j) (by
      rintro _ ⟨y, rfl⟩
      exact y.property)

omit [Mono j] [Etale q.left] in
@[reassoc]
theorem affineSeed_toOpen : affineSeed e a j z ≫ affineToOpen e a j z =
    (affineSeedDomain e a j z).ι ≫ seed e a j := IsOpenImmersion.lift_fac _ _ _

omit [Etale q.left] in
/-- The seed's coefficient projection is a literal composite of open inclusions. -/
@[reassoc]
theorem affineSeed_target : affineSeed e a j z ≫
    (affineToOpen e a j z ≫ projection a j) =
      (affineSeedDomain e a j z).ι ≫ (seedOpen e a j).ι := by
  rw [← Category.assoc, affineSeed_toOpen, Category.assoc, seed_projection]

/-- All two-sided etale and monic seed properties are proved for this genuine affine chart. -/
theorem affineSeed_geometry : Etale (affineSeed e a j z) ∧
    Etale (affineSeed e a j z ≫ (affineToOpen e a j z ≫ projection a j)) ∧
    Mono (affineSeed e a j z ≫ (affineToOpen e a j z ≫ projection a j)) := by
  let _ : IsOpenImmersion
      (affineSeed e a j z ≫ (affineToOpen e a j z ≫ projection a j)) := by
    rw [affineSeed_target]
    infer_instance
  exact ⟨Etale.of_comp _ (affineToOpen e a j z ≫ projection a j),
    inferInstance, inferInstance⟩

omit [Mono j] [Etale q.left] in
/-- The chosen affine seed retains the precise original parameter morphism. -/
@[reassoc]
theorem affineSeed_parameter : affineSeed e a j z ≫ affineChart e a j z =
    (affineSeedDomain e a j z).ι ≫ (seedOpen e a j).ι ≫
      SchemeRelationSplitOrbit.sectionMap e a ≫ j := by
  rw [affineChart, ← Category.assoc, affineSeed_toOpen, Category.assoc, seed_parameter]

end FLT.Mazur.SchemeOrbitOpenSelection
