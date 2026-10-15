/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IndependentGroundCartesianTransport
public import FLT.Mazur.AffineHilbertFixedBaseEnvelope

/-!
# Original relation sections on Cartesian ground overlaps

Pull a section from an original envelope to a full translation base change.
Its original relation equation constructs compatibility across independent
new-ground maps, using the canonical whole-envelope transport. No equality
of the new ground maps, norm equation, or extended source section is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open HilbertChart.AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (B W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (H : IsPullback t.left W.hom V.hom a)
  {A D : Over (Spec (.of R))} (u : (Over.map a).obj B ⟶ A)
  (p q : D ⟶ A) {T : Scheme} (x y : T ⟶ B.left) (z : T ⟶ D.left)
  (hx : z ≫ p.left = x ≫ u.left) (hy : z ≫ q.left = y ≫ u.left)

include hx hy in
/-- Original relation arrows identify the old grounds, while retaining both new ones. -/
theorem originalRelation_ground_eq : (x ≫ B.hom) ≫ a = (y ≫ B.hom) ≫ a := by
  have hp := p.w
  have hq := q.w
  have hu := u.w
  change u.left ≫ A.hom = B.hom ≫ a at hu
  rw [Category.assoc, ← hu, ← Category.assoc, ← hx, Category.assoc, hp]
  rw [Category.assoc, ← hu, ← Category.assoc, ← hy, Category.assoc, hq]

/-- Every original relation arrow lifts to its entire independent old translation envelope. -/
def originalRelationEnvelopeLift : independentTestEnvelope B W x ⟶ (prod D V).left :=
  (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd D V)).lift
    (independentTestProjection B W x ≫ z) (independentOldTranslation V B W t.left x) (by
      have hu := u.w
      change u.left ≫ A.hom = B.hom ≫ a at hu
      rw [Category.assoc, ← p.w, ← Category.assoc z, hx, Category.assoc, hu]
      simpa only [Category.assoc] using
        (independentEnvelope_old_isPullback a V B W t.left H x).w)

/-- The constructed lift retains the whole original relation morphism. -/
@[reassoc]
theorem originalRelationEnvelopeLift_fst :
    originalRelationEnvelopeLift a V B W t H u p x z hx ≫
      (prod.fst : prod D V ⟶ D).left = independentTestProjection B W x ≫ z :=
  IsPullback.lift_fst _ _ _ _

/-- The lift retains the old independent translation coordinate. -/
@[reassoc]
theorem originalRelationEnvelopeLift_snd :
    originalRelationEnvelopeLift a V B W t H u p x z hx ≫
      (prod.snd : prod D V ⟶ V).left = independentOldTranslation V B W t.left x :=
  IsPullback.lift_snd _ _ _ _

/-- Pullback of the envelope retains its entire source morphism. -/
@[reassoc]
theorem independentTestEnvelopeMap_projection :
    independentTestEnvelopeMap B W x ≫ (prod.fst : prod B W ⟶ B).left =
      independentTestProjection B W x ≫ x :=
  congrArg Over.Hom.left (prod.map_fst (independentTestArrow B x) (𝟙 W))

/-- Pullback of the envelope retains its independent translation. -/
@[reassoc]
theorem independentTestEnvelopeMap_translation :
    independentTestEnvelopeMap B W x ≫ (prod.snd : prod B W ⟶ W).left =
      (prod.snd : prod (independentTest B x) W ⟶ W).left := by
  exact congrArg Over.Hom.left
    ((prod.map_snd (independentTestArrow B x) (𝟙 W)).trans (Category.comp_id _))

/-- The source endpoint of the lift is the actual pulled-back old envelope map. -/
theorem originalRelationEnvelopeLift_left :
    originalRelationEnvelopeLift a V B W t H u p x z hx ≫
      (prod.map p (𝟙 V)).left =
        independentTestEnvelopeMap B W x ≫ (fixedBaseEnvelopeMap a V W t u).left := by
  have hf := congrArg Over.Hom.left (fixedBaseEnvelopeMap_fst a V W t u)
  have hs := congrArg Over.Hom.left (fixedBaseEnvelopeMap_snd a V W t u)
  simp only [Over.comp_left, Over.map_map_left] at hf hs
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).hom_ext
  · change _ ≫ _ ≫ (prod.fst : prod A V ⟶ A).left =
      _ ≫ _ ≫ (prod.fst : prod A V ⟶ A).left
    rw [← Over.comp_left, prod.map_fst, Over.comp_left, hf,
      originalRelationEnvelopeLift_fst_assoc, hx,
      independentTestEnvelopeMap_projection_assoc]
  · change _ ≫ _ ≫ (prod.snd : prod A V ⟶ V).left =
      _ ≫ _ ≫ (prod.snd : prod A V ⟶ V).left
    rw [← Over.comp_left, prod.map_snd, Category.comp_id, hs,
      originalRelationEnvelopeLift_snd, independentTestEnvelopeMap_translation_assoc]
    rfl

local notation "h" => originalRelation_ground_eq a B u p q x y z hx hy
local notation "e" => cartesianGroundTransport a V B W t.left H x y h

/-- The target endpoint is the actual other envelope map after constructed ground transport. -/
theorem originalRelationEnvelopeLift_right :
    originalRelationEnvelopeLift a V B W t H u p x z hx ≫
      (prod.map q (𝟙 V)).left =
        (e).hom ≫ independentTestEnvelopeMap B W y ≫
          (fixedBaseEnvelopeMap a V W t u).left := by
  have hf := congrArg Over.Hom.left (fixedBaseEnvelopeMap_fst a V W t u)
  have hs := congrArg Over.Hom.left (fixedBaseEnvelopeMap_snd a V W t u)
  simp only [Over.comp_left, Over.map_map_left] at hf hs
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).hom_ext
  · change _ ≫ _ ≫ (prod.fst : prod A V ⟶ A).left =
      _ ≫ _ ≫ _ ≫ (prod.fst : prod A V ⟶ A).left
    rw [← Over.comp_left, prod.map_fst, Over.comp_left, hf,
      originalRelationEnvelopeLift_fst_assoc, hy,
      independentTestEnvelopeMap_projection_assoc,
      cartesianGroundTransport_projection_assoc]
  · change _ ≫ _ ≫ (prod.snd : prod A V ⟶ V).left =
      _ ≫ _ ≫ _ ≫ (prod.snd : prod A V ⟶ V).left
    rw [← Over.comp_left, prod.map_snd, Category.comp_id, hs,
      originalRelationEnvelopeLift_snd, independentTestEnvelopeMap_translation_assoc]
    change _ = (e).hom ≫ independentOldTranslation V B W t.left y
    exact (cartesianGroundTransport_translation a V B W t.left H x y h).symm

/-- An original section equation supplies the chosen-section transport, including nilpotents. -/
theorem cartesianEnvelope_section_transport (s : Γ((prod A V).left, ⊤))
    (hs : (prod.map p (𝟙 V)).left.appTop s = (prod.map q (𝟙 V)).left.appTop s) :
    (e).hom.appTop ((independentTestEnvelopeMap B W y).appTop
      ((fixedBaseEnvelopeMap a V W t u).left.appTop s)) =
        (independentTestEnvelopeMap B W x).appTop
          ((fixedBaseEnvelopeMap a V W t u).left.appTop s) := by
  have he := congrArg
    (fun r ↦ (originalRelationEnvelopeLift a V B W t H u p x z hx).appTop r) hs
  change ((originalRelationEnvelopeLift a V B W t H u p x z hx) ≫
    (prod.map p (𝟙 V)).left).appTop s =
      ((originalRelationEnvelopeLift a V B W t H u p x z hx) ≫
        (prod.map q (𝟙 V)).left).appTop s at he
  rw [originalRelationEnvelopeLift_left,
    originalRelationEnvelopeLift_right a V B W t H u p q x y z hx hy] at he
  exact he.symm

end FLT.Mazur.SchemeTranslationNorm
