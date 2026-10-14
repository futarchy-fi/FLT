/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOrbitOpenSelection

/-!
# Full original relations on the constructed open parameter selections

Pull back the entire original orbit relation along both selected endpoints.
Its comparison is an isomorphism by base change of the constructed full orbit
kernel isomorphism. The resulting surjective etale quotient descends scheme
maps uniquely and preserves all coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOrbitOpenSelection
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T Z H : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
  (j : pullback q.left a ⟶ H) [Mono j] [Mono (pullback.lift p.left q.left h)]
local notation "π" => pullback.snd q.left a
local notation "v" => projection a j
local notation "l" => MonomorphismOpenImage.lift j
local notation "r" => SchemeRelationSplitOrbit.fullComparison w h a

/-- Keep both independently chosen original orbit endpoints of the new kernel. -/
def kernelToOrbit : pullback v v ⟶ pullback π π :=
  pullback.lift (pullback.fst v v ≫ l) (pullback.snd v v ≫ l) (by
    simpa only [projection, Category.assoc] using pullback.condition (f := v) (g := v))

/-- The full original relation restricted along both selected parameter endpoints. -/
def relation : Scheme := pullback r (kernelToOrbit a j)

/-- The actual comparison to the complete new projection kernel. -/
def comparison : relation w h a j ⟶ pullback v v := pullback.snd r (kernelToOrbit a j)

/-- The unchanged original relation arrow, retaining its full scheme structure. -/
def originalArrow : relation w h a j ⟶ D.left :=
  pullback.fst r (kernelToOrbit a j) ≫ SchemeRelationSplitOrbit.fullArrow w h a

include e in
/-- Effectivity survives restriction of both endpoints without any old unramifiedness. -/
theorem comparison_isIso : IsIso (comparison w h a j) := by
  let _ : IsIso r := (SchemeRelationSplitOrbit.fullKernelIso e w h a).isIso_hom
  exact inferInstanceAs (IsIso (pullback.snd r (kernelToOrbit a j)))

include e in
/-- The full original relation is the kernel of the complete selected projection. -/
theorem relation_isPullback : IsPullback
    (comparison w h a j ≫ pullback.fst v v)
    (comparison w h a j ≫ pullback.snd v v) v v := by
  let _ := comparison_isIso e w h a j
  exact IsPullback.of_iso_pullback
    ⟨by simp only [Category.assoc, pullback.condition]⟩
    (asIso (comparison w h a j)) rfl rfl

omit [Mono (pullback.lift p.left q.left h)] in
/-- The original first endpoint remains the selected original orbit point. -/
@[reassoc]
theorem originalArrow_fst : originalArrow w h a j ≫ p.left =
    comparison w h a j ≫ pullback.fst v v ≫ l ≫
      SchemeRelationEtaleBranchPropagation.branch p.left q.left a := by
  rw [originalArrow, Category.assoc,
    (SchemeRelationSplitOrbit.fullRelation_endpoints w h a).1, ← Category.assoc]
  change (pullback.fst r (kernelToOrbit a j) ≫ r) ≫ _ = _
  rw [pullback.condition]
  simp only [Category.assoc, kernelToOrbit, pullback.lift_fst_assoc, comparison]

omit [Mono (pullback.lift p.left q.left h)] in
/-- The independent second endpoint is preserved as well. -/
@[reassoc]
theorem originalArrow_snd : originalArrow w h a j ≫ q.left =
    comparison w h a j ≫ pullback.snd v v ≫ l ≫
      SchemeRelationEtaleBranchPropagation.branch p.left q.left a := by
  rw [originalArrow, Category.assoc,
    (SchemeRelationSplitOrbit.fullRelation_endpoints w h a).2, ← Category.assoc]
  change (pullback.fst r (kernelToOrbit a j) ≫ r) ≫ _ = _
  rw [pullback.condition]
  simp only [Category.assoc, kernelToOrbit, pullback.lift_snd_assoc, comparison]

variable [Etale q.left]
include e in
/-- Passing to the actual open image retains this entire original relation kernel. -/
theorem quotient_isPullback : IsPullback
    (comparison w h a j ≫ pullback.fst v v)
    (comparison w h a j ≫ pullback.snd v v) (quotient a j) (quotient a j) :=
  SchemeEtaleImageQuotient.isPullback v (relation_isPullback e w h a j)

include e in
/-- Actual morphisms descend from the full original relation to the constructed scheme quotient. -/
theorem existsUnique_descend {Y : Scheme} (t : (parameterOpen a j).toScheme ⟶ Y)
    (ht : (comparison w h a j ≫ pullback.fst v v) ≫ t =
      (comparison w h a j ≫ pullback.snd v v) ≫ t) :
    ∃! g : (targetOpen a j).toScheme ⟶ Y, quotient a j ≫ g = t := by
  let H := relation_isPullback e w h a j
  exact ⟨SchemeEtaleImageQuotient.descend v H t ht,
    SchemeEtaleImageQuotient.projection_descend v H t ht,
    fun g hg ↦ SchemeEtaleImageQuotient.descend_unique v H t ht g hg⟩

end FLT.Mazur.SchemeOrbitOpenSelection
