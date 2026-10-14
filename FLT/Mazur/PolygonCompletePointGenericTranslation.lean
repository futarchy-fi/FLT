/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginalGenericGroup
public import FLT.Mazur.PolygonCompleteSmoothFieldTranslation

/-!
# Original generic rotations are translations in the complete identity group

Use the proved pointed group comparison, with retained identity label zero.
The translating point is the unchanged original cyclic section, expressed in
the base change of the constructed complete-base identity group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation translation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "H" => Functor.obj (Functor.mapCommGrp (Over.pullback s)) (G)
local notation "E" => completePointOriginalGenericGroupIso K n h L a ha p q hs (0 : Fin n)
local notation "u" => Scheme.Opens.ι (completePointIdentityOpen K n h (0 : Fin n))

/-- The unchanged original cyclic section in coordinates of the complete identity group. -/
def completePointGenericCyclicPoint (b : ZMod n) : 𝟙_ (Over (Spec (.of L))) ⟶ (H).X :=
  completeCyclicSection K n h s p q hs b ≫ (E).inv.hom.hom.hom

/-- The translating point projects to precisely the original complete cyclic marking. -/
@[reassoc] theorem completePointGenericCyclicPoint_original (b : ZMod n) :
    (completePointGenericCyclicPoint K n h L a ha p q hs b).left ≫
      pullback.fst (G).X.hom s ≫ u = s ≫ completeBaseMarking K n h ((ZMod.finEquiv n).symm b) := by
  change ((completeCyclicSection K n h s p q hs b).left ≫
    (E).inv.hom.hom.hom.left) ≫ pullback.fst (G).X.hom s ≫ u = _
  rw [Category.assoc, completePointOriginalGenericGroupIso_inv_original]
  exact completeCartesianMarking_fst K n h s p q hs ((ZMod.finEquiv n).symm b)

/-- The translating sections retain the original cyclic addition law. -/
theorem completePointGenericCyclicPoint_add (b c : ZMod n) :
    completePointGenericCyclicPoint K n h L a ha p q hs (b + c) =
      completePointGenericCyclicPoint K n h L a ha p q hs b *
        completePointGenericCyclicPoint K n h L a ha p q hs c := by
  let _ := completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)
  have he := (completeFieldCyclicPointHom K n h L a ha p q hs).map_mul
    (Multiplicative.ofAdd b) (Multiplicative.ofAdd c)
  simp only [completeFieldCyclicPointHom_apply] at he
  change completeCyclicSection K n h s p q hs (b + c) =
    completeCyclicSection K n h s p q hs b * completeCyclicSection K n h s p q hs c at he
  change completeCyclicSection K n h s p q hs (b + c) ≫ (E).inv.hom.hom.hom = _
  rw [he, MonObj.mul_comp]
  rfl

/-- Negating the original cyclic label inverts its translating section. -/
theorem completePointGenericCyclicPoint_neg (b : ZMod n) :
    completePointGenericCyclicPoint K n h L a ha p q hs (-b) =
      (completePointGenericCyclicPoint K n h L a ha p q hs b)⁻¹ := by
  let _ := completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)
  have he := map_inv (completeFieldCyclicPointHom K n h L a ha p q hs)
    (Multiplicative.ofAdd b)
  simp only [completeFieldCyclicPointHom_apply] at he
  change completeCyclicSection K n h s p q hs (-b) =
    (completeCyclicSection K n h s p q hs b)⁻¹ at he
  change completeCyclicSection K n h s p q hs (-b) ≫ (E).inv.hom.hom.hom = _
  rw [he, GrpObj.inv_comp]
  rfl

/-- Inverting translated coordinates negates their original chart label. -/
theorem completePointGenericTranslation_inv (b : ZMod n) {T : Over (Spec (.of L))}
    (x : T ⟶ (H).X) :
    (x ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs b))⁻¹ =
      x⁻¹ ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs (-b)) := by
  rw [comp_translation, comp_translation, completePointGenericCyclicPoint_neg,
    GrpObj.comp_inv, mul_inv_rev]
  exact mul_comm _ _

/-- Translating the two inputs adds their original chart labels in the output. -/
theorem completePointGenericTranslation_mul (b c : ZMod n) {T : Over (Spec (.of L))}
    (x y : T ⟶ (H).X) :
    (x ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs b)) *
      (y ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs c)) =
        (x * y) ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs (b + c)) := by
  rw [comp_translation, comp_translation, comp_translation,
    completePointGenericCyclicPoint_add, MonObj.comp_mul]
  exact mul_mul_mul_comm _ _ _ _

/-- Original rotations act as translations on every test scheme in the complete group. -/
theorem completePointGenericRotation_test (b : ZMod n) {T : Over (Spec (.of L))}
    (x : T ⟶ (H).X) :
    x ≫ (E).hom.hom.hom.hom ≫ completeCartesianRotationOver K n h s p q hs b ≫
      (E).inv.hom.hom.hom =
        (toUnit T ≫ completePointGenericCyclicPoint K n h L a ha p q hs b) * x := by
  let _ := completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)
  rw [← Category.assoc x, ← Category.assoc,
    completeFieldRotation_test, MonObj.mul_comp]
  have he := congrArg (fun k ↦ k.hom.hom.hom) (E).hom_inv_id
  change (E).hom.hom.hom.hom ≫ (E).inv.hom.hom.hom = 𝟙 _ at he
  rw [Category.assoc x, he, Category.comp_id]
  rfl

/-- Conjugating the original field rotation gives translation in the complete identity group. -/
theorem completePointGenericRotation_eq_translation (b : ZMod n) :
    (E).hom.hom.hom.hom ≫ completeCartesianRotationOver K n h s p q hs b ≫
      (E).inv.hom.hom.hom =
        translation (completePointGenericCyclicPoint K n h L a ha p q hs b) := by
  simpa only [Category.id_comp, translation] using
    completePointGenericRotation_test K n h L a ha p q hs b (𝟙 (H).X)

/-- The forward group comparison retains the actual original family projection. -/
@[reassoc] theorem completePointGenericGroupIso_hom_original :
    (E).hom.hom.hom.hom.left ≫ p = pullback.fst (G).X.hom s ≫ u := by
  have he := congrArg (fun k ↦ k.hom.hom.hom.left) (E).hom_inv_id
  change (E).hom.hom.hom.hom.left ≫ (E).inv.hom.hom.hom.left = 𝟙 _ at he
  calc
    (E).hom.hom.hom.hom.left ≫ p = (E).hom.hom.hom.hom.left ≫
        (E).inv.hom.hom.hom.left ≫ pullback.fst (G).X.hom s ≫ u :=
      congrArg ((E).hom.hom.hom.hom.left ≫ ·)
        (completePointOriginalGenericGroupIso_inv_original K n h L a ha p q hs 0).symm
    _ = _ := by rw [← Category.assoc, he, Category.id_comp]

/-- Translation in the complete identity group is the actual original generic rotation. -/
@[reassoc] theorem completePointGenericTranslation_original (b : ZMod n) :
    (translation (completePointGenericCyclicPoint K n h L a ha p q hs b)).left ≫
      pullback.fst (G).X.hom s ≫ u =
        pullback.fst (G).X.hom s ≫ u ≫ completeRotation K n h b := by
  have he := congrArg (fun k : (H).X ⟶ (H).X ↦
    k.left ≫ pullback.fst (G).X.hom s ≫ u)
      (completePointGenericRotation_eq_translation K n h L a ha p q hs b)
  simp only [Over.comp_left, Category.assoc,
    completePointOriginalGenericGroupIso_inv_original] at he
  rw [← he]
  change (E).hom.hom.hom.hom.left ≫ completeCartesianRotation K n h s p q hs b ≫ p = _
  rw [completeCartesianRotation_fst, ← Category.assoc,
    completePointGenericGroupIso_hom_original, Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages
