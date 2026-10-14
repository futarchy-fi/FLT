/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorProjection

/-!
# Original ground maps on the glued selector quotient

The original base morphism descends on each constructed quotient and then
through the scheme gluing. The assembled etale source projection is a
morphism over that unchanged ground, including its structure-sheaf map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSeedSelector.Data
set_option backward.isDefEq.respectTransparency false
variable {S B : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  {k : B ⟶ A.left} (d : Data p q k)

/-- Original arrows force preservation of the original ground by representatives. -/
@[reassoc]
theorem representative_ground : d.rep ≫ k ≫ A.hom = k ≫ A.hom := by
  rw [← Category.assoc, ← d.target, Category.assoc, q.w, ← p.w,
    ← Category.assoc, d.source]

/-- The constructed quotient projection respects the original ground morphism. -/
@[reassoc]
theorem projection_ground : d.projection ≫ (d.inclusion ≫ k ≫ A.hom) = k ≫ A.hom := by
  rw [projection_inclusion_assoc, representative_ground]

end FLT.Mazur.SchemeRelationSeedSelector.Data

namespace FLT.Mazur.SchemeRelationOpenSelector
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]

/-- The ground map of an actual constructed quotient chart. -/
def chartGround (U : Chart p q) : (selector p q U).quotient ⟶ S :=
  (selector p q U).inclusion ≫ U.val.val.ι ≫ A.hom

omit [Etale q.left] in
/-- All quotient transitions respect the unchanged original base. -/
@[reassoc]
theorem transition_ground {U V : Chart p q} (h : U ≤ V) :
    transition p q h ≫ chartGround V = chartGround U := by
  apply (selector p q U).hom_ext
  rw [projection_transition_assoc]
  change A.left.homOfLE h ≫ (selector p q V).projection ≫
    ((selector p q V).inclusion ≫ V.val.val.ι ≫ A.hom) =
      (selector p q U).projection ≫ ((selector p q U).inclusion ≫ U.val.val.ι ≫ A.hom)
  rw [SchemeRelationSeedSelector.Data.projection_ground,
    SchemeRelationSeedSelector.Data.projection_ground, Scheme.homOfLE_ι_assoc]

/-- The ground morphism is constructed by the scheme colimit universal property. -/
def ground : glued e ⟶ S := colimit.desc (diagram p q e)
  { pt := S
    ι := { app := chartGround
           naturality := fun U V h ↦ by
             change transition p q (leOfHom h) ≫ chartGround V = chartGround U ≫ 𝟙 S
             rw [Category.comp_id]
             exact transition_ground (leOfHom h) } }

/-- The glued ground map restricts to the literal chart ground maps. -/
@[reassoc]
theorem chartMap_ground (U : Chart p q) : chartMap e U ≫ ground e = chartGround U :=
  colimit.ι_desc _ U

/-- The projection from the ORIGINAL source union preserves its original base morphism. -/
@[reassoc]
theorem projection_ground : projection e ≫ ground e =
    (sourceOpen (p := p) (q := q)).ι ≫ A.hom := by
  apply openImageUnion_hom_ext (fun U : Chart p q ↦ U.val.val.ι)
  intro U
  rw [chart_projection_assoc, sourceMap, Category.assoc, chartMap_ground]
  change (selector p q U).projection ≫ chartGround U =
    openImageUnionMap (fun V : Chart p q ↦ V.val.val.ι) U ≫
      (openImageUnion (fun V : Chart p q ↦ V.val.val.ι)).ι ≫ A.hom
  rw [openImageUnionMap_fac_assoc]
  exact (selector p q U).projection_ground

/-- The assembled quotient remains a scheme over the original ground. -/
def relativeGlued : Over S := Over.mk (ground e)

/-- Its etale surjection is an actual morphism over the original ground. -/
def relativeProjection : Over.mk ((sourceOpen (p := p) (q := q)).ι ≫ A.hom) ⟶
    relativeGlued e := Over.homMk (projection e) (projection_ground e)

end FLT.Mazur.SchemeRelationOpenSelector
