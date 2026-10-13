/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFppfLocallyRingedCover

/-!
# Full locally ringed coequalizers under fppf refinement

A covering comparison on sources and full relations preserves their locally
ringed coequalizers when the source kernel pair maps to the upper relation.
All hypotheses concern actual scheme maps; neither quotient is assumed a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationFppfRefinement
open RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U B T : Over S} (p q : A ⟶ U) (r s : B ⟶ T)
  (g : U ⟶ T) (h : A ⟶ B)
  (hp : h ≫ r = p ≫ g) (hq : h ≫ s = q ≫ g)
  [Flat g.left] [LocallyOfFinitePresentation g.left] [Surjective g.left]
  [Flat h.left] [LocallyOfFinitePresentation h.left] [Surjective h.left]
  (k : pullback g g ⟶ A) (kp : k ≫ p = pullback.fst g g)
  (kq : k ≫ q = pullback.snd g g)
local notation "Q₁" => locallyRingedQuotient (p := p) (q := q)
local notation "Q₂" => locallyRingedQuotient (p := r) (q := s)
local notation "π₁" => locallyRingedProjection (p := p) (q := q)
local notation "π₂" => locallyRingedProjection (p := r) (q := s)

local instance : Epi π₁ := by
  dsimp only [locallyRingedProjection]
  infer_instance

local instance : Epi π₂ := by
  dsimp only [locallyRingedProjection]
  infer_instance

omit [Flat g.left] [LocallyOfFinitePresentation g.left] [Surjective g.left] in
include k kp kq in
/-- The original source quotient map agrees on the actual source kernel pair. -/
theorem kernel_condition :
    (pullback.fst g g).left.toLRSHom ≫ π₁ = (pullback.snd g g).left.toLRSHom ≫ π₁ := by
  rw [← kp, ← kq, Over.comp_left, Over.comp_left, Scheme.Hom.comp_toLRSHom,
    Scheme.Hom.comp_toLRSHom, Category.assoc, Category.assoc]
  exact congrArg (fun a ↦ k.left.toLRSHom ≫ a) (coequalizer.condition _ _)

/-- Descend the original quotient map along the actual source cover. -/
def descendedProjection : T.left.toLocallyRingedSpace ⟶ Q₁ :=
  RelativeFppfLocallyRingedCover.descend g π₁ (kernel_condition p q g k kp kq)

/-- Descent recovers the entire original quotient projection. -/
@[reassoc]
theorem descendedProjection_source :
    g.left.toLRSHom ≫ descendedProjection p q g k kp kq = π₁ :=
  RelativeFppfLocallyRingedCover.descend_projection g π₁ (kernel_condition p q g k kp kq)

include h hp hq in
/-- Compatibility descends along the cover of the full relation, including mixed pairs. -/
theorem descendedProjection_condition :
    r.left.toLRSHom ≫ descendedProjection p q g k kp kq =
      s.left.toLRSHom ≫ descendedProjection p q g k kp kq := by
  let _ := RelativeFppfLocallyRingedCover.epi h
  apply (cancel_epi h.left.toLRSHom).mp
  have hp' := congrArg (fun a ↦ a.left.toLRSHom) hp
  have hq' := congrArg (fun a ↦ a.left.toLRSHom) hq
  simp only [Over.comp_left, Scheme.Hom.comp_toLRSHom] at hp' hq'
  rw [← Category.assoc, hp', Category.assoc, descendedProjection_source,
    ← Category.assoc, hq', Category.assoc, descendedProjection_source]
  exact coequalizer.condition _ _

/-- The full quotient comparison from the lower presentation back to the refinement. -/
def backward : Q₂ ⟶ Q₁ :=
  coequalizer.desc (descendedProjection p q g k kp kq)
    (descendedProjection_condition p q r s g h hp hq k kp kq)

/-- The forward map is induced by the actual source comparison. -/
def forward : Q₁ ⟶ Q₂ :=
  coequalizer.desc (g.left.toLRSHom ≫ π₂) (by
    have hp' := congrArg (fun a ↦ a.left.toLRSHom) hp
    have hq' := congrArg (fun a ↦ a.left.toLRSHom) hq
    simp only [Over.comp_left, Scheme.Hom.comp_toLRSHom] at hp' hq'
    dsimp only [locallyRingedProjection]
    rw [← Category.assoc, ← hp', Category.assoc, coequalizer.condition,
      ← Category.assoc, hq', Category.assoc])

omit [Flat g.left] [LocallyOfFinitePresentation g.left] [Surjective g.left]
  [Flat h.left] [LocallyOfFinitePresentation h.left] [Surjective h.left] in
/-- The forward comparison retains the original source arrow. -/
@[reassoc]
theorem forward_source : π₁ ≫ forward p q r s g h hp hq = g.left.toLRSHom ≫ π₂ :=
  coequalizer.π_desc _ _

/-- The backward comparison retains the descended source projection. -/
@[reassoc]
theorem backward_source : π₂ ≫ backward p q r s g h hp hq k kp kq =
    descendedProjection p q g k kp kq := coequalizer.π_desc _ _

/-- Fppf refinement preserves the full locally ringed quotient, including regular functions. -/
def quotientIso : Q₁ ≅ Q₂ where
  hom := forward p q r s g h hp hq
  inv := backward p q r s g h hp hq k kp kq
  hom_inv_id := by
    apply (cancel_epi π₁).mp
    rw [forward_source_assoc, backward_source,
      descendedProjection_source, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi π₂).mp
    rw [backward_source_assoc, Category.comp_id]
    let _ := RelativeFppfLocallyRingedCover.epi g
    apply (cancel_epi g.left.toLRSHom).mp
    rw [descendedProjection_source_assoc, forward_source]

/-- The quotient isomorphism has the prescribed original source equation. -/
@[reassoc]
theorem quotientIso_source : π₁ ≫ (quotientIso p q r s g h hp hq k kp kq).hom =
    g.left.toLRSHom ≫ π₂ := forward_source p q r s g h hp hq

/-- The isomorphism preserves the original coefficient morphism. -/
theorem quotientIso_base :
    (quotientIso p q r s g h hp hq k kp kq).hom ≫
      locallyRingedBaseMap (p := r) (q := s) = locallyRingedBaseMap (p := p) (q := q) := by
  apply (cancel_epi π₁).mp
  rw [quotientIso_source_assoc, locallyRingedProjection_baseMap,
    locallyRingedProjection_baseMap, ← Scheme.Hom.comp_toLRSHom, Over.w]

end FLT.Mazur.RelativeRelationFppfRefinement
