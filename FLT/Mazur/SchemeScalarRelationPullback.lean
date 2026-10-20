/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationScalarSupportedBaseChange

/-!
# Full relation coefficients on an actual scalar pullback

Both endpoints are pulled over the same scalar map. Their section equalizer
retains the entire relation and the unreduced test scheme. A coefficient with
exact pulled relation equations gives an element of this actual equalizer.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarRelationPullback
variable {X D S Y : Scheme} (p q : D ⟶ X) (s : X ⟶ S)
  (hs : p ≫ s = q ≫ s) (b : Y ⟶ S)

/-- The unchanged source after scalar base change. -/
abbrev testSource : Scheme := pullback s b

/-- The full relation after scalar base change along its first endpoint. -/
abbrev testRelation : Scheme := pullback (p ≫ s) b

/-- The first endpoint on the actual source pullback. -/
def testFirst : testRelation p s b ⟶ testSource s b :=
  pullback.lift (pullback.fst (p ≫ s) b ≫ p) (pullback.snd (p ≫ s) b)
    (by rw [Category.assoc, pullback.condition])

/-- The independent second endpoint uses scalar compatibility, not endpoint identification. -/
def testSecond : testRelation p s b ⟶ testSource s b :=
  pullback.lift (pullback.fst (p ≫ s) b ≫ q) (pullback.snd (p ≫ s) b)
    (by rw [Category.assoc, ← hs, pullback.condition])

@[simp]
theorem testFirst_fst :
    testFirst p s b ≫ pullback.fst s b = pullback.fst (p ≫ s) b ≫ p :=
  pullback.lift_fst _ _ _

@[simp]
theorem testSecond_fst :
    testSecond p q s hs b ≫ pullback.fst s b = pullback.fst (p ≫ s) b ≫ q :=
  pullback.lift_fst _ _ _

/-- The full coefficient equalizer on the actual unreduced source test. -/
def testInvariants : Subring Γ(testSource s b, ⊤) :=
  RingHom.eqLocus (testFirst p s b).appTop.hom (testSecond p q s hs b).appTop.hom

/-- An original function belongs to this equalizer exactly when its full test equations hold. -/
theorem pullback_mem_testInvariants_iff (a : Γ(X, ⊤)) :
    (pullback.fst s b).appTop a ∈ testInvariants p q s hs b ↔
      (pullback.fst (p ≫ s) b ≫ p).appTop a =
        (pullback.fst (p ≫ s) b ≫ q).appTop a := by
  change (testFirst p s b).appTop ((pullback.fst s b).appTop a) =
    (testSecond p q s hs b).appTop ((pullback.fst s b).appTop a) ↔ _
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    testFirst_fst, testSecond_fst]

/-- The actual lifted element of the full relation equalizer. -/
def invariantLift (a : Γ(X, ⊤))
    (ha : (pullback.fst (p ≫ s) b ≫ p).appTop a =
      (pullback.fst (p ≫ s) b ≫ q).appTop a) : testInvariants p q s hs b :=
  ⟨(pullback.fst s b).appTop a, (pullback_mem_testInvariants_iff p q s hs b a).mpr ha⟩

/-- A genuine boundary map induces restriction on the full test equalizer. -/
def testBoundaryRestriction {Z : Scheme} (i : Z ⟶ X) :
    testInvariants p q s hs b →+* Γ(pullback (i ≫ s) b, ⊤) :=
  (testFirst i s b).appTop.hom.comp (testInvariants p q s hs b).subtype

/-- Boundary values of an invariant lift are the original exact boundary values pulled back. -/
theorem testBoundaryRestriction_lift {Z : Scheme} (i : Z ⟶ X)
    (a : Γ(X, ⊤))
    (ha : (pullback.fst (p ≫ s) b ≫ p).appTop a =
      (pullback.fst (p ≫ s) b ≫ q).appTop a) :
    testBoundaryRestriction p q s hs b i (invariantLift p q s hs b a ha) =
      (pullback.fst (i ≫ s) b).appTop (i.appTop a) := by
  change (testFirst i s b).appTop ((pullback.fst s b).appTop a) = _
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, testFirst_fst]

end FLT.Mazur.SchemeScalarRelationPullback
