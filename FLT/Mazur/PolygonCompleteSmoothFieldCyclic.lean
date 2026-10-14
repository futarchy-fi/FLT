/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldGroup
public import FLT.Mazur.PolygonCompleteCyclicMarking
public import FLT.Mazur.PolygonProjectiveExactTorsion
public import FLT.Mazur.ConstantCyclicSectionMap

/-!
# The original finite marking is a homomorphism on the smooth field fiber

Transport the already proved cyclic point homomorphism from the constructed
cubic to the original entire curve. The resulting sections are the original
unshifted labels when label zero is the identity. Coproduct descent then proves
that the original marking scheme map preserves the full smooth group law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "S" => Spec (CommRingCat.of L)
local notation "e" => completeFieldCubicOverIso K n h L a ha p q hs (0 : Fin n)
local notation "cg" => completeFieldCubicCommGrp K n h L a ha p q hs (0 : Fin n)
local notation "fg" => completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)

/-- The original unshifted labels are a homomorphism into the full original field curve. -/
def completeFieldCyclicPointHom :
    let _ := fg
    Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ Over.mk q) := by
  let _ := cg
  let _ := fg
  let _ : IsMonHom (e).inv := isMonHom_ofIso (e).symm
  let u : 𝟙_ (Over S) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L L))) :=
    Over.homMk (𝟙 S) (by simp)
  let φ := completeProjectiveCyclicPointHom K n h L a ha p q hs (0 : Fin n)
  exact
    { toFun := fun b ↦ u ≫ φ b ≫ (e).inv
      map_one' := by rw [map_one, MonObj.one_comp, MonObj.comp_one]
      map_mul' := fun b c ↦ by rw [map_mul, MonObj.mul_comp, MonObj.comp_mul] }

/-- The transported cyclic section is exactly the original complete marked section. -/
theorem completeFieldCyclicPointHom_apply (b : Multiplicative (ZMod n)) :
    completeFieldCyclicPointHom K n h L a ha p q hs b =
      completeCyclicSection K n h s p q hs b.toAdd := by
  let _ := cg
  let _ := fg
  apply Over.OverMorphism.ext
  change (𝟙 S ≫ (completeCartesianMarking K n h s p q hs
    (rotateIndex b.toAdd (0 : Fin n)) ≫ (e).hom.left) ≫ (e).inv.left) = _
  rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
    Over.id_left]
  simp only [Over.mk_left, Category.comp_id, completeCyclicSection, Over.homMk_left,
    rotateIndex, map_zero, zero_add]

/-- Descent of the proved section homomorphism recovers the entire original marking map. -/
theorem completeFieldCyclicPointHom_toScheme :
    let _ := fg
    ConstantCyclicSectionMap.toScheme (completeFieldCyclicPointHom K n h L a ha p q hs) =
      completeCyclicMarking K n h s p q hs := by
  let _ := fg
  apply Sigma.hom_ext
  intro b
  change ConstantCyclicGroup.component S n b ≫ _ = _
  rw [ConstantCyclicSectionMap.component_toScheme, completeFieldCyclicPointHom_apply,
    completeCyclicMarking_component]
  rfl

/-- The original entire constant cyclic marking scheme embeds by a group homomorphism. -/
theorem completeCyclicMarking_field_isMonHom :
    let _ := fg
    IsMonHom (completeCyclicMarking K n h s p q hs) := by
  let _ := fg
  rw [← completeFieldCyclicPointHom_toScheme K n h L a ha p q hs]
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
