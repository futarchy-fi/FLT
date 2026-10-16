/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointFrameGraph
public import FLT.Mazur.EquivalenceRelationBoundarySubframeGeometry

/-!
# Entire common-frame overlaps of independently chosen source charts

The two charts may have unrelated sizes and unrelated affine refinements.
Their overlap is the intersection of both full inverse images. Its boundary
maps retain the original closed subschemes, not only their geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H] (o : I) (o' : J)
  (α : I ↪ H) (β : J ↪ H)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)

/-- The entire common-source overlap of the independently selected charts. -/
def jointChartOpen : (source p q H (α o)).Opens :=
  subframeMap e (α o) o α ⁻¹ᵁ U ⊓ subframeMap e (α o) o' β ⁻¹ᵁ V

/-- The first chart projection from the entire common-source overlap. -/
def jointChartFirst : (jointChartOpen e o o' α β U V).toScheme ⟶ U.toScheme :=
  (subframeMap e (α o) o α).resLE U _ inf_le_left

/-- The second chart projection from the entire common-source overlap. -/
def jointChartSecond : (jointChartOpen e o o' α β U V).toScheme ⟶ V.toScheme :=
  (subframeMap e (α o) o' β).resLE V _ inf_le_right

/-- The first projection retains the whole subframe map on the actual open. -/
@[reassoc] theorem jointChartFirst_inclusion :
    jointChartFirst e o o' α β U V ≫ U.ι =
      (jointChartOpen e o o' α β U V).ι ≫ subframeMap e (α o) o α :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The second projection retains the whole subframe map on the actual open. -/
@[reassoc] theorem jointChartSecond_inclusion :
    jointChartSecond e o o' α β U V ≫ V.ι =
      (jointChartOpen e o o' α β U V).ι ≫ subframeMap e (α o) o' β :=
  Scheme.Hom.resLE_comp_ι _ _

variable (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "j" => InvariantBoundary.inclusion (p := p) (q := q) H (α o) i
local notation "j₁" => InvariantBoundary.inclusion (p := p) (q := q) I o i
local notation "j₂" => InvariantBoundary.inclusion (p := p) (q := q) J o' i
local notation "W" => jointChartOpen e o o' α β U V

/-- The full closed overlap maps to the first chart's full closed boundary. -/
def jointChartBoundaryFirst : ((j) ⁻¹ᵁ W).toScheme ⟶ ((j₁) ⁻¹ᵁ U).toScheme :=
  (subframeBoundaryMap e (α o) o i z r s hr hs α).resLE _ _ (by
    rw [← Scheme.Hom.comp_preimage, subframeBoundaryMap_inclusion,
      Scheme.Hom.comp_preimage]
    exact fun _ hx ↦ hx.1)

/-- The full closed overlap maps to the second chart's full closed boundary. -/
def jointChartBoundarySecond : ((j) ⁻¹ᵁ W).toScheme ⟶ ((j₂) ⁻¹ᵁ V).toScheme :=
  (subframeBoundaryMap e (α o) o' i z r s hr hs β).resLE _ _ (by
    rw [← Scheme.Hom.comp_preimage, subframeBoundaryMap_inclusion,
      Scheme.Hom.comp_preimage]
    exact fun _ hx ↦ hx.2)

omit [Mono i] in
/-- The first closed chart square commutes on the entire overlap scheme. -/
@[reassoc] theorem jointChartBoundaryFirst_inclusion :
    jointChartBoundaryFirst e o o' α β U V i z r s hr hs ≫ ((j₁) ∣_ U) =
      ((j) ∣_ W) ≫ jointChartFirst e o o' α β U V := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, morphismRestrict_ι, jointChartBoundaryFirst,
    Scheme.Hom.resLE_comp_ι_assoc, jointChartFirst_inclusion,
    subframeBoundaryMap_inclusion, morphismRestrict_ι_assoc]

omit [Mono i] in
/-- The second closed chart square commutes on the entire overlap scheme. -/
@[reassoc] theorem jointChartBoundarySecond_inclusion :
    jointChartBoundarySecond e o o' α β U V i z r s hr hs ≫ ((j₂) ∣_ V) =
      ((j) ∣_ W) ≫ jointChartSecond e o o' α β U V := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, morphismRestrict_ι, jointChartBoundarySecond,
    Scheme.Hom.resLE_comp_ι_assoc, jointChartSecond_inclusion,
    subframeBoundaryMap_inclusion, morphismRestrict_ι_assoc]

/-- Independent chart restrictions keep the first exact Cartesian boundary square. -/
theorem jointChartBoundaryFirst_isPullback :
    IsPullback (jointChartBoundaryFirst e o o' α β U V i z r s hr hs)
      ((j) ∣_ W) ((j₁) ∣_ U) (jointChartFirst e o o' α β U V) := by
  simpa only [jointChartBoundaryFirst, jointChartBoundarySecond, jointChartFirst,
    jointChartSecond, Scheme.Hom.resLE_eq_morphismRestrict] using
    (Scheme.Hom.isPullback_resLE
    (subframeBoundaryMap_isPullback e (α o) o i z r s hr hs α)
    (show W ≤ subframeMap e (α o) o α ⁻¹ᵁ U from inf_le_left) le_rfl (show (j) ⁻¹ᵁ W = _ from by
      rw [← Scheme.Hom.comp_preimage, subframeBoundaryMap_inclusion,
        Scheme.Hom.comp_preimage]
      exact (inf_eq_right.mpr (fun _ hx ↦ hx.1)).symm))

/-- Independent chart restrictions keep the second exact Cartesian boundary square. -/
theorem jointChartBoundarySecond_isPullback :
    IsPullback (jointChartBoundarySecond e o o' α β U V i z r s hr hs)
      ((j) ∣_ W) ((j₂) ∣_ V) (jointChartSecond e o o' α β U V) := by
  simpa only [jointChartBoundaryFirst, jointChartBoundarySecond, jointChartFirst,
    jointChartSecond, Scheme.Hom.resLE_eq_morphismRestrict] using
    (Scheme.Hom.isPullback_resLE
    (subframeBoundaryMap_isPullback e (α o) o' i z r s hr hs β)
    (show W ≤ subframeMap e (α o) o' β ⁻¹ᵁ V from inf_le_right) le_rfl (show (j) ⁻¹ᵁ W = _ from by
      rw [← Scheme.Hom.comp_preimage, subframeBoundaryMap_inclusion,
        Scheme.Hom.comp_preimage]
      exact (inf_eq_right.mpr (fun _ hx ↦ hx.2)).symm))

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
