/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteThickeningTower
public import FLT.Mazur.EquivalenceRelationCompleteEquivariantCoefficients

/-!
# Full original coefficient compatibility through all complete infinitesimal orders

The actual stage invariant rings form an inverse system. Every coefficient in
this system equalizes its entire original two-endpoint relation, not merely
its action graphs on reduced points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- Actual invariant coordinates on the full positive power quotient. -/
abbrev completeStageCoordinates (k : ℕ) := invariantCoordinates (completeThickeningAction e I o k)

/-- Coordinate restriction is pullback along the actual closed stage transition. -/
def completeStageRestriction {m n : ℕ} (h : m ≤ n) :
    completeStageCoordinates e I o n →+* completeStageCoordinates e I o m :=
  invariantMap (completeThickeningAction e I o m) (completeThickeningAction e I o n)
    (completeThickeningTransition I o h) (completeThickeningTransition_equivariant I o e h)

/-- The invariant restriction retains the exact original coefficient pullback. -/
theorem completeStageRestriction_val {m n : ℕ} (h : m ≤ n)
    (t : completeStageCoordinates e I o n) :
    (completeStageRestriction e I o h t).val =
      (completeThickeningTransition I o h).appTop t.val := rfl

/-- Restrictions through any three orders agree. -/
theorem completeStageRestriction_comp {l m n : ℕ} (h : l ≤ m) (h' : m ≤ n)
    (t : completeStageCoordinates e I o n) :
    completeStageRestriction e I o h (completeStageRestriction e I o h' t) =
      completeStageRestriction e I o (h.trans h') t := by
  apply Subtype.ext
  simp only [completeStageRestriction_val]
  change (((completeThickeningTransition I o h').appTop ≫
    (completeThickeningTransition I o h).appTop) t.val) = _
  rw [← Scheme.Hom.comp_appTop, completeThickeningTransition_comp]

/-- Every invariant stage coefficient satisfies the full original self-mixed equation. -/
theorem completeStageCoordinates_equalizes (k : ℕ) (t : completeStageCoordinates e I o k) :
    (SourceRestriction.fst (completeThickeningInclusion I o k)
      (completeThickeningInclusion I o k)).appTop t.val =
    (SourceRestriction.snd (completeThickeningInclusion I o k)
      (completeThickeningInclusion I o k)).appTop t.val :=
  completeEquivariant_invariant_equalizes e I o (completeThickeningInclusion I o k)
    (completeThickeningAction e I o k) (completeThickeningActionMap_inclusion e I o k)
    (completeThickeningInclusion_range I o k).le t

/-- Every arbitrary original-arrow test retains exact stage coefficient compatibility. -/
theorem completeStageCoordinates_test (k : ℕ) (t : completeStageCoordinates e I o k)
    {T : Scheme.{0}} (u v : T ⟶ completeThickening (p := p) (q := q) I o k) (a : T ⟶ D)
    (ha : a ≫ p = u ≫ completeThickeningInclusion I o k ≫ first p q I o)
    (hb : a ≫ q = v ≫ completeThickeningInclusion I o k ≫ first p q I o) :
    u.appTop t.val = v.appTop t.val :=
  completeEquivariant_invariant_test e I o (completeThickeningInclusion I o k)
    (completeThickeningAction e I o k) (completeThickeningActionMap_inclusion e I o k)
    (completeThickeningInclusion_range I o k).le t u v a ha hb

end FLT.Mazur.EquivalenceRelationNormalizedFrames
