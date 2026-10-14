/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldTranslation
public import FLT.Mazur.PolygonCompleteSmoothFieldSubgroup
public import FLT.Mazur.ConstantCyclicActionDescent

/-!
# The original whole cyclic action is the full field subgroup action

Coproduct descent upgrades the translation law to equality of scheme actions.
The actual product divisor acts through its unchanged subgroup inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "S" => Spec (CommRingCat.of L)
local notation "fg" => completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)
local notation "E" => completeFieldGeneralizedCurve K n h L a ha p q hs (0 : Fin n)

/-- The original entire cyclic action is multiplication by the original marking homomorphism. -/
theorem completeCyclicAction_field_eq :
    let _ := fg
    completeCyclicAction K n h s p q hs =
      completeCyclicMarking K n h s p q hs ▷ Over.mk q ≫ μ[Over.mk q] := by
  let _ := fg
  change completeCyclicAction K n h s p q hs =
    completeCyclicMarking K n h s p q hs ▷ Over.mk q ≫ μ[Over.mk q]
  symm
  apply ConstantCyclicSchemeAction.act_unique
  intro b
  rw [← comp_whiskerRight_assoc, completeCyclicMarking_component,
    completeFieldRotation_eq_translation K n h L a ha p q hs]
  simp only [MonObj.mul_eq_mul, MonObj.comp_mul, whiskerRight_fst, whiskerRight_snd,
    translation, Category.comp_id, leftUnitor_hom]
  congr 1
  rw [← Category.assoc]
  exact congrArg (· ≫ completeCyclicSection K n h s p q hs b) (toUnit_unique _ _)

/-- The original cyclic scheme action is the restriction of the actual full DR action. -/
theorem completeCyclicAction_field_DR :
    completeCyclicAction K n h s p q hs =
      completeCyclicMarking K n h s p q hs ▷ (E).curve ≫ (E).act :=
  completeCyclicAction_field_eq K n h L a ha p q hs

/-- The actual original divisor acts by its inclusion into the full smooth group. -/
def completeFieldDivisorAction :
    (completeFieldFiniteSubgroup K n h L a ha p q hs).carrier ⊗ (E).curve ⟶ (E).curve :=
  (completeFieldFiniteSubgroup K n h L a ha p q hs).inclusion ▷ (E).curve ≫ (E).act

/-- The action on the product divisor is exactly the original entire cyclic action. -/
theorem completeFieldDivisorAction_original :
    (completeCyclicDivisorIso K n h s p q hs).hom ▷ (E).curve ≫
      completeFieldDivisorAction K n h L a ha p q hs =
        completeCyclicAction K n h s p q hs := by
  rw [completeFieldDivisorAction, ← comp_whiskerRight_assoc]
  change ((completeCyclicDivisorIso K n h s p q hs).hom ≫
    (completeCyclicDivisorIso K n h s p q hs).inv ≫
      completeCyclicMarking K n h s p q hs) ▷ (E).curve ≫ (E).act = _
  rw [Iso.hom_inv_id_assoc, ← completeCyclicAction_field_DR]

end FLT.Mazur.PolygonInfinitesimalStages
