/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSplitOrbitKernel

/-!
# Split effective scheme quotients of original orbits

The quotient is the entire seed scheme. Descent is given by its constructed
reflexive section and tests the full original relation, including both new
coordinates. The projection is a surjective etale map when the original
second endpoint is etale. Coefficient and ground maps survive as scheme maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSplitOrbit
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
  [Mono (pullback.lift p.left q.left h)]
local notation "B" => (pullback q.left a : Scheme)
local notation "π" => pullback.snd q.left a
local notation "r₁" => fullComparison w h a ≫ pullback.fst π π
local notation "r₂" => fullComparison w h a ≫ pullback.snd π π
variable {Y : Scheme.{u}} (t : pullback q.left a ⟶ Y)
  (ht : (fullComparison w h a ≫ pullback.fst (pullback.snd q.left a)
    (pullback.snd q.left a)) ≫ t =
      (fullComparison w h a ≫ pullback.snd (pullback.snd q.left a)
        (pullback.snd q.left a)) ≫ t)

/-- Descent is the actual reflexive section followed by the given scheme map. -/
def descend : Z ⟶ Y := sectionMap e a ≫ t

include ht in
/-- Full original relation compatibility gives the desired factorization as scheme maps. -/
@[reassoc]
theorem projection_descend : π ≫ descend e a t = t := by
  let H := fullRelation_isPullback e w h a
  let j := H.lift (𝟙 B) (π ≫ sectionMap e a) (by
    rw [Category.id_comp, Category.assoc, sectionMap_projection, Category.comp_id])
  have he := congrArg (fun g ↦ j ≫ g) ht
  have h₁ : j ≫ r₁ = 𝟙 B := H.lift_fst _ _ _
  have h₂ : j ≫ r₂ = π ≫ sectionMap e a := H.lift_snd _ _ _
  simpa only [descend, ← Category.assoc, h₁, h₂, Category.id_comp] using he.symm

/-- Uniqueness uses the constructed section and does not assume an abstract quotient. -/
theorem descend_unique (g : Z ⟶ Y) (hg : π ≫ g = t) : g = descend e a t := by
  rw [descend, ← hg, ← Category.assoc, sectionMap_projection, Category.id_comp]

include e ht in
/-- The full original changed relation has the entire seed scheme as effective quotient. -/
theorem existsUnique_descend : ∃! g : Z ⟶ Y, π ≫ g = t :=
  ⟨descend e a t, projection_descend e w h a t ht, fun g hg ↦ descend_unique e a t g hg⟩

/-- Any retained coefficient morphism is preserved by the scheme descent. -/
@[reassoc]
theorem descend_coefficient {Q : Scheme.{u}} (c : Y ⟶ Q) (v : Z ⟶ Q)
    (hv : t ≫ c = π ≫ v) : descend e a t ≫ c = v := by
  rw [descend, Category.assoc, hv, ← Category.assoc,
    sectionMap_projection, Category.id_comp]

include e in
omit [Mono (pullback.lift p.left q.left h)] in
/-- The quotient is a constructed fppf cover of its WHOLE target. -/
theorem projection_cover [Etale q.left] : Etale π ∧ Surjective π :=
  ⟨inferInstance, projection_surjective e a⟩

include e in
omit [Mono (pullback.lift p.left q.left h)] in
/-- Every scheme test has a COMPLETE surjective etale source pullback. -/
theorem complete_cover [Etale q.left] {Y : Scheme.{u}} (v : Y ⟶ Z) :
    Etale (pullback.snd π v) ∧ Surjective (pullback.snd π v) := by
  let _ := projection_surjective e a
  exact ⟨inferInstance, inferInstance⟩

end FLT.Mazur.SchemeRelationSplitOrbit
