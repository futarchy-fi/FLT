/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveActionPullback
public import FLT.Mazur.PolygonFieldExtension
public import FLT.Mazur.PolygonActionBaseChange

/-!
# The polygon action in actual field-extension coordinates

Finite coproduct comparison identifies the pulled-back split smooth group.
Projective-line action comparison, followed by the epic normalization,
identifies the intrinsic extension-field action with the actual pulled-back action.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonActionFieldExtension
open PolygonPinching PolygonUniversalAction ProjectiveLineProductCharts
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
local notation "F" => Over.pullback (parameterToBase K L)

/-- Extension-field coordinates on the actual pulled-back split smooth group. -/
def groupIso (n : ℕ) [NeZero n] : G L n ≅ (F).obj (G K n) :=
  PolygonFieldExtension.coproductIso K L _ _
    (fun _ ↦ MultiplicativeGroupFieldExtension.equivalence K L)

@[reassoc (attr := simp)] theorem group_inclusion (n : ℕ) [NeZero n] (b : ZMod n) :
    PolygonSplitGroup.component L n b ≫ (groupIso K L n).hom =
      (MultiplicativeGroupFieldExtension.equivalence K L).hom ≫
        (F).map (PolygonSplitGroup.component K n b) :=
  PolygonFieldExtension.inclusion K L _ _ _ b

variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The actual normalization after extension, in projective-line coordinates. -/
abbrev normalization := (PolygonFieldExtension.componentsIso K L n).hom ≫ (F).map p
/-- The actual node map after extension, in field-point coordinates. -/
abbrev nodeMap := (PolygonFieldExtension.nodesIso K L n).hom ≫ (F).map q
include h in
/-- The actual extension-field polygon cocone. -/
theorem cocone : IsPushout (toComponents L n hn) (toNodes L n)
    (normalization K L n p) (nodeMap K L n q) :=
  PolygonFieldExtension.isPushout K L n hn p q h

omit [NeZero n] in
@[reassoc (attr := simp)] theorem component_normalization (i : Fin n) :
    componentι L n i ≫ normalization K L n p =
      (ProjectiveLineFieldExtension.componentIso K L).hom ≫
        (F).map (componentι K n i ≫ p) := by
  simp [normalization, PolygonFieldExtension.componentsIso, componentι, Functor.map_comp]

/-- The intrinsic action in extension-field coordinates equals the actual pulled-back action. -/
theorem action :
    (groupIso K L n).hom ▷ (F).obj C ≫
      PolygonActionBaseChange.baseChangedAct K n hn p q h (parameterToBase K L) =
    act L n hn (normalization K L n p) (nodeMap K L n q) (cocone K L n hn p q h) := by
  let : Epi (G L n ◁ normalization K L n p) :=
    PolygonActionAssociativity.tensor_normalization_epi L n hn _ _ (cocone K L n hn p q h) _
  apply (cancel_epi (G L n ◁ normalization K L n p)).mp
  apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod n ↦ gm L)
    (fun _ : Fin n ↦ component L)
  intro b i
  change (PolygonSplitGroup.component L n b ⊗ₘ componentι L n i) ≫ _ = _
  rw [tensorHom_comp_whiskerLeft_assoc, tensorHom_comp_whiskerLeft_assoc,
    tensorHom_comp_whiskerRight_assoc, group_inclusion, component_normalization]
  erw [component_act L n hn (normalization K L n p) (nodeMap K L n q)
    (cocone K L n hn p q h) b i]
  rw [PolygonActionBaseChange.baseChangedAct, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp,
    component_act K n hn p q h b i, Functor.map_comp, Functor.map_comp]
  rw [reassoc_of% (ProjectiveActionPullback.action K L)]
  simp [component_normalization, Functor.map_comp]
end FLT.Mazur.PolygonActionFieldExtension
