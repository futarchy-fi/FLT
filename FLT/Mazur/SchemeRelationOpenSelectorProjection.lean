/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorGluing
public import FLT.Mazur.OpenImmersionImageUnionGluing

/-!
# The original source projection to the glued selector scheme

The invariant source opens form an actual open union in the original
parameter scheme. Their constructed quotient maps glue to an etale
surjection onto the assembled scheme, without choosing global representatives.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]

/-- The map from each original source open to the glued quotient. -/
def sourceMap (U : Chart p q) : U.val.val.toScheme ⟶ glued e :=
  (selector p q U).projection ≫ chartMap e U

/-- Source maps agree under all literal original open inclusions. -/
@[reassoc]
theorem inclusion_sourceMap {U V : Chart p q} (h : U ≤ V) :
    A.left.homOfLE h ≫ sourceMap e V = sourceMap e U := by
  rw [sourceMap, ← projection_transition_assoc, transition_chartMap]
  rfl

/-- The common original source overlap maps to its intersection chart. -/
def overlapToIntersection (U V : Chart p q) :
    pullback U.val.val.ι V.val.val.ι ⟶ (intersection p q U V).val.val.toScheme :=
  IsOpenImmersion.lift (intersection p q U V).val.val.ι
    (pullback.fst U.val.val.ι V.val.val.ι ≫ U.val.val.ι) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨_, (pullback.fst U.val.val.ι V.val.val.ι x).property, ?_⟩, rfl⟩
      have h := congrArg (fun a ↦ a x)
        (pullback.condition (f := U.val.val.ι) (g := V.val.val.ι))
      change (pullback.fst U.val.val.ι V.val.val.ι ≫ U.val.val.ι) x ∈ V.val.val
      rw [h]
      exact (pullback.snd U.val.val.ι V.val.val.ι x).property)

/-- Source compatibility is proved on full scheme overlaps, not only their points. -/
theorem sourceMap_compatible (U V : Chart p q) :
    pullback.fst U.val.val.ι V.val.val.ι ≫ sourceMap e U =
      pullback.snd U.val.val.ι V.val.val.ι ≫ sourceMap e V := by
  let a := overlapToIntersection U V
  have ha : a ≫ (intersection p q U V).val.val.ι =
      pullback.fst U.val.val.ι V.val.val.ι ≫ U.val.val.ι := IsOpenImmersion.lift_fac _ _ _
  have hU : a ≫ A.left.homOfLE (intersection_le_left p q U V) =
      pullback.fst U.val.val.ι V.val.val.ι := by
    apply (cancel_mono U.val.val.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι, ha]
  have hV : a ≫ A.left.homOfLE (intersection_le_right p q U V) =
      pullback.snd U.val.val.ι V.val.val.ι := by
    apply (cancel_mono V.val.val.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι, ha, pullback.condition]
  rw [← hU, ← hV, Category.assoc, Category.assoc,
    inclusion_sourceMap, inclusion_sourceMap]

/-- The actual union of all original invariant opens admitting representatives. -/
def sourceOpen : A.left.Opens := openImageUnion (fun U : Chart p q ↦ U.val.val.ι)

omit [Etale q.left] in
/-- The union is saturated for the complete original relation. -/
theorem sourceOpen_invariant :
    p.left ⁻¹ᵁ sourceOpen (p := p) (q := q) = q.left ⁻¹ᵁ sourceOpen (p := p) (q := q) := by
  have mem (x : A.left) : x ∈ sourceOpen (p := p) (q := q) ↔
      ∃ U : Chart p q, x ∈ U.val.val := by
    simp only [sourceOpen, openImageUnion, Scheme.Opens.opensRange_ι,
      TopologicalSpace.Opens.mem_iSup]
  ext z
  change p.left z ∈ sourceOpen (p := p) (q := q) ↔
    q.left z ∈ sourceOpen (p := p) (q := q)
  rw [mem, mem]
  exact exists_congr (fun U ↦ Set.ext_iff.mp (congrArg SetLike.coe U.val.property) z)

/-- The assembled projection from the literal original source open. -/
def projection : (sourceOpen (p := p) (q := q)).toScheme ⟶ glued e :=
  openImageUnionGlue (fun U : Chart p q ↦ U.val.val.ι) (sourceMap e) (sourceMap_compatible e)

/-- Each original parameter chart has its constructed quotient map after gluing. -/
@[reassoc]
theorem chart_projection (U : Chart p q) :
    openImageUnionMap (fun V : Chart p q ↦ V.val.val.ι) U ≫ projection e = sourceMap e U :=
  openImageUnionGlue_fac _ _ _ U

/-- The glued projection is etale, proved on the original source open cover. -/
theorem projection_etale : Etale (projection e) := by
  apply IsZariskiLocalAtSource.of_openCover
    (openImageUnionCover (fun U : Chart p q ↦ U.val.val.ι))
  intro U
  change Etale (openImageUnionMap _ U ≫ projection e)
  rw [chart_projection, sourceMap]
  let _ := (selector p q U).projection_etale e
  infer_instance

/-- Every glued quotient point has an actual original source lift. -/
theorem projection_surjective : Surjective (projection e) := ⟨fun z ↦ by
  obtain ⟨U, x, hx⟩ := exists_original e z
  refine ⟨openImageUnionMap (fun V : Chart p q ↦ V.val.val.ι) U x, ?_⟩
  have h := congrArg (fun a ↦ a x) (chart_projection e U)
  exact h.trans hx⟩

end FLT.Mazur.SchemeRelationOpenSelector
