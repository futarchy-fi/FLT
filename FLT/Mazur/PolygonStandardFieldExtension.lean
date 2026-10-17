/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFieldExtension
public import FLT.Mazur.PolygonAtlas

/-!
# The chosen standard polygon after field extension

The specified normalization and node comparisons identify the independently
chosen standard polygon over the new field with the actual base change.
This also treats the one-gon target of contraction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonStandardFieldExtension
open PolygonPinching PolygonFieldExtension
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K L : Type) [Field K] [Field L] [Algebra K L]
local notation "F" => Over.pullback (ProjectiveLineProductCharts.parameterToBase K L)
variable (n : ℕ) [NeZero n] (hn : 0 < n)

/-- The actual chosen standard polygon, compared over the extension field. -/
def iso : PolygonAtlas.polygon L n ≅ (F).obj (PolygonAtlas.polygon K n) :=
  (PolygonAtlas.isPushout L n hn).isoIsPushout _ _
    (PolygonFieldExtension.isPushout K L n hn _ _ (PolygonAtlas.isPushout K n hn))

/-- The comparison keeps the entire specified normalization coproduct. -/
@[reassoc] theorem normalization_iso :
    PolygonAtlas.normalization L n ≫ (iso K L n hn).hom =
      (componentsIso K L n).hom ≫ (F).map (PolygonAtlas.normalization K n) :=
  (PolygonAtlas.isPushout L n hn).inl_isoIsPushout_hom _ _ _

/-- The comparison keeps all original pinching nodes. -/
@[reassoc] theorem nodes_iso :
    PolygonAtlas.nodes L n ≫ (iso K L n hn).hom =
      (nodesIso K L n).hom ≫ (F).map (PolygonAtlas.nodes K n) :=
  (PolygonAtlas.isPushout L n hn).inr_isoIsPushout_hom _ _ _

/-- Each original complete component is carried by its specified coefficient-change isomorphism. -/
@[reassoc] theorem component_iso (j : Fin n) :
    componentι L n j ≫ PolygonAtlas.normalization L n ≫ (iso K L n hn).hom =
      (ProjectiveLineFieldExtension.componentIso K L).hom ≫
        (F).map (componentι K n j ≫ PolygonAtlas.normalization K n) := by
  rw [normalization_iso, Functor.map_comp]
  change Sigma.ι _ j ≫ (coproductIso K L _ _ _).hom ≫ _ = _
  rw [inclusion_assoc]
  rfl

/-- Each original coefficient node is carried by the specified point comparison. -/
@[reassoc] theorem node_iso (j : Fin n) :
    nodeι L n j ≫ PolygonAtlas.nodes L n ≫ (iso K L n hn).hom =
      (ProjectiveLineFieldExtension.pointIso K L).hom ≫
        (F).map (nodeι K n j ≫ PolygonAtlas.nodes K n) := by
  rw [nodes_iso, Functor.map_comp]
  change Sigma.ι _ j ≫ (coproductIso K L _ _ _).hom ≫ _ = _
  rw [inclusion_assoc]
  rfl

/-- Component and node equations uniquely determine the standard comparison. -/
theorem hom_unique (d : PolygonAtlas.polygon L n ⟶ (F).obj (PolygonAtlas.polygon K n))
    (hp : PolygonAtlas.normalization L n ≫ d =
      (componentsIso K L n).hom ≫ (F).map (PolygonAtlas.normalization K n))
    (hq : PolygonAtlas.nodes L n ≫ d =
      (nodesIso K L n).hom ≫ (F).map (PolygonAtlas.nodes K n)) :
    d = (iso K L n hn).hom := by
  apply (PolygonAtlas.isPushout L n hn).hom_ext
  · exact hp.trans (normalization_iso K L n hn).symm
  · exact hq.trans (nodes_iso K L n hn).symm

end FLT.Mazur.PolygonStandardFieldExtension
