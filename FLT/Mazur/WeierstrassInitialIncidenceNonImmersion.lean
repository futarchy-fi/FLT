/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInitialIncidenceCollisionPoints

/-!
# The original incidence pair is not a full initial chart embedding

Two distinct rational points on the same entire initial neighborhood have
identical incidence coordinates. Thus this candidate morphism is not mono
and cannot be used as an open immersion in the polygon atlas.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.InitialIncidenceCollision
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
local notation "A" => Coordinate curve 0 0 0 0
local notation "O" => PolynomialInitialOpen curve 0 0 0 0 (0 : ℚ[X])

/-- The full incidence morphism restricted to the original initial open. -/
def openIncidenceMap : PolygonSmoothing.ChartRing (0 : ℚ) →ₐ[ℚ] O :=
  (Algebra.algHom ℚ A O).comp (incidencePolygonMap curve 0 0 0 0)

/-- Passing to the original initial open preserves the entire incidence map. -/
theorem openSlopePoint_incidence (c : ℚ) (hc : c + 1 ≠ 0) :
    (openSlopePoint c hc).comp openIncidenceMap =
      (slopePoint c).comp (incidencePolygonMap curve 0 0 0 0) := by
  apply AlgHom.ext
  intro z
  exact openSlopePoint_base c hc _

/-- The collision persists on the full localized domain, not just on its ambient chart. -/
theorem openSlopePoint_incidence_collision :
    (openSlopePoint 1 (by norm_num)).comp openIncidenceMap =
      (openSlopePoint (-2) (by norm_num)).comp openIncidenceMap := by
  rw [openSlopePoint_incidence, openSlopePoint_incidence,
    incidencePolygonMap, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    slopePoint_incidence_collision]

/-- The actual proposed full initial morphism in polygon coordinates. -/
def openIncidenceMorphism : Spec (.of O) ⟶ PolygonSmoothing.chart ℚ 0 :=
  Spec.map (CommRingCat.ofHom openIncidenceMap.toRingHom)

/-- This candidate is exactly the restriction of the original incidence morphism. -/
theorem openIncidenceMorphism_eq : openIncidenceMorphism =
    polynomialInitialOpenInclusion curve 0 0 0 0 (0 : ℚ[X]) ≫
      incidencePolygonMorphism curve 0 0 0 0 := by
  rw [polynomialInitialOpenInclusion, incidencePolygonMorphism, ← Spec.map_comp]
  rfl

/-- Equal images of the two explicit rational points rule out monomorphism. -/
theorem openIncidenceMorphism_not_mono : ¬ Mono openIncidenceMorphism := by
  intro hm
  let _ := hm
  let f := Spec.map (CommRingCat.ofHom (openSlopePoint 1 (by norm_num)).toRingHom)
  let g := Spec.map (CommRingCat.ofHom (openSlopePoint (-2) (by norm_num)).toRingHom)
  have he : f ≫ openIncidenceMorphism = g ≫ openIncidenceMorphism := by
    dsimp only [f, g, openIncidenceMorphism]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h.toRingHom))
      openSlopePoint_incidence_collision
  have he' : f = g := (cancel_mono openIncidenceMorphism).mp he
  apply openSlopePoint_one_ne_neg_two
  exact AlgHom.coe_ringHom_injective
    (congrArg CommRingCat.Hom.hom (Spec.map_injective he'))

/-- In particular, dividing p by its opposite factor does not give a full chart embedding. -/
theorem openIncidenceMorphism_not_isOpenImmersion :
    ¬ IsOpenImmersion openIncidenceMorphism := by
  intro h
  let _ := h
  exact openIncidenceMorphism_not_mono inferInstance

end FLT.Mazur.InitialIncidenceCollision
