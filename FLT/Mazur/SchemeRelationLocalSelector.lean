/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSelectorEtale
public import FLT.Mazur.SchemeRelationEtaleCoverDescent

/-!
# Constructing global selectors from compatible local original arrows

Local arrows on an etale source cover need only have invariant second endpoints
on the FULL two-coordinate relation. Joint monicity then proves their descent
compatibility, constructing a global selector and hence an effective quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationLocalSelector
open SchemeRelationRestriction RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (k : Z ⟶ A.left)
  (r : Z ⟶ D.left) (hr : r ≫ p.left = k)
local notation "x" => fst p.left q.left k
local notation "y" => snd p.left q.left k

include e hr in
/-- Full relation invariance of the targets forces descent compatibility of actual arrows. -/
theorem compatible (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left)
    {Y : Scheme.{u}} (a b : Y ⟶ Z) (h : a ≫ k = b ≫ k) : a ≫ r = b ≫ r := by
  apply originalArrow_ext e
  · simpa only [Category.assoc, hr] using h
  · simpa only [Category.assoc] using
      SchemeRelationEtaleCoverDescent.kernel_compatible e k (r ≫ q.left) hi a b h

variable [Etale k] [Surjective k]

/-- Descent constructs an actual family of original arrows on the original source. -/
def selector (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left) : A.left ⟶ D.left :=
  EffectiveEpi.desc k r (compatible e k r hr hi)

@[reassoc]
theorem cover_selector (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left) :
    k ≫ selector e k r hr hi = r := EffectiveEpi.fac k r _

/-- The constructed family starts at the literal original parameter, over its original base. -/
@[reassoc]
theorem selector_fst (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left) :
    selector e k r hr hi ≫ p.left = 𝟙 A.left := by
  apply (cancel_epi k).mp
  rw [cover_selector_assoc, hr, Category.comp_id]

/-- Both coordinates of the full relation cover detect global representative invariance. -/
theorem selector_invariant (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left) :
    p.left ≫ selector e k r hr hi ≫ q.left =
      q.left ≫ selector e k r hr hi ≫ q.left := by
  apply (cancel_epi (arrow p.left q.left k)).mp
  simp only [← Category.assoc, arrow_fst, arrow_snd]
  simpa only [Category.assoc, cover_selector_assoc] using hi

/-- Local original arrow data construct a scheme quotient target. -/
def target (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left) : Scheme.{u} :=
  SchemeRelationSelectorQuotient.target (q := q) (selector e k r hr hi)

/-- Its projection is built from the descended arrows, with no supplied kernel model. -/
def projection (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left) : A.left ⟶ target e k r hr hi :=
  SchemeRelationSelectorQuotient.projection (selector e k r hr hi)
    (selector_fst e k r hr hi) (selector_invariant e k r hr hi)

/-- The full original scheme relation is the kernel of the locally constructed quotient. -/
theorem isPullback (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left) :
    IsPullback p.left q.left (projection e k r hr hi) (projection e k r hr hi) :=
  SchemeRelationSelectorQuotient.isPullback e (selector e k r hr hi)
    (selector_fst e k r hr hi) (selector_invariant e k r hr hi)

/-- Etale geometry and surjectivity are conclusions of the local arrow construction. -/
theorem cover (hi : x ≫ r ≫ q.left = y ≫ r ≫ q.left) [Etale q.left] :
    Etale (projection e k r hr hi) ∧ Surjective (projection e k r hr hi) :=
  ⟨SchemeRelationSelectorQuotient.projection_etale e (selector e k r hr hi)
    (selector_fst e k r hr hi) (selector_invariant e k r hr hi),
    SchemeRelationSelectorQuotient.projection_surjective (selector e k r hr hi)
      (selector_fst e k r hr hi) (selector_invariant e k r hr hi)⟩

end FLT.Mazur.SchemeRelationLocalSelector
