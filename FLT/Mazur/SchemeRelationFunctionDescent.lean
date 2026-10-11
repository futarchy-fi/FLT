/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Descent of invariant functions through a covering relation comparison

A cover of sources and an epimorphic comparison of relations identify their
invariant function rings, provided the source cover's kernel pair maps to the
upstairs relation. All conditions concern actual scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections
variable {X Y A B K : Scheme.{u}} {p q : A ⟶ X} {a b : B ⟶ Y}
  (g : Y ⟶ X) (k : B ⟶ A)
  (h₁ : k ≫ p = a ≫ g) (h₂ : k ≫ q = b ≫ g)

include k h₁ h₂

/-- Pulling back an invariant function preserves the actual relation equation. -/
theorem relationFunction_pullback (s : compatibleFunctions p q) :
    g.appTop s.val ∈ compatibleFunctions a b := by
  change a.appTop (g.appTop s.val) = b.appTop (g.appTop s.val)
  change (a ≫ g).appTop s.val = (b ≫ g).appTop s.val
  rw [← h₁, ← h₂]
  change k.appTop (p.appTop s.val) = k.appTop (q.appTop s.val)
  exact congrArg k.appTop s.property

/-- The actual pullback homomorphism on invariant function rings. -/
def relationFunctionPullback : compatibleFunctions p q →+* compatibleFunctions a b :=
  (g.appTop.hom.comp (compatibleFunctions p q).subtype).codRestrict _
    (relationFunction_pullback g k h₁ h₂)

/-- An epimorphic relation comparison detects invariance of a descended function. -/
theorem relationFunction_invariant [Epi k] (s : Γ(X, ⊤))
    (hs : g.appTop s ∈ compatibleFunctions a b) : s ∈ compatibleFunctions p q := by
  apply appTop_injective k
  change (k ≫ p).appTop s = (k ≫ q).appTop s
  rw [h₁, h₂]
  exact hs

variable [EffectiveEpi g] [Epi k] {r t : K ⟶ Y}
  (H : IsPullback r t g g) (l : K ⟶ B) (hl₁ : l ≫ a = r) (hl₂ : l ≫ b = t)

include H l hl₁ hl₂

/-- Every upstairs invariant function descends to a unique downstairs invariant function. -/
theorem relationFunction_existsUnique (s : compatibleFunctions a b) :
    ∃! v : compatibleFunctions p q, g.appTop v.val = s.val := by
  have hs : r.appTop s.val = t.appTop s.val := by
    rw [← hl₁, ← hl₂]
    change l.appTop (a.appTop s.val) = l.appTop (b.appTop s.val)
    exact congrArg l.appTop s.property
  obtain ⟨v, hv, _⟩ := sections_existsUnique H s.val hs
  have hi : v ∈ compatibleFunctions p q :=
    relationFunction_invariant g k h₁ h₂ v (hv ▸ s.property)
  exact ⟨⟨v, hi⟩, hv, fun w hw ↦ Subtype.ext (appTop_injective g (hw.trans hv.symm))⟩

/-- The two original invariant-function rings agree by effective descent of regular functions. -/
def relationFunctionRingEquiv : compatibleFunctions p q ≃+* compatibleFunctions a b := by
  apply RingEquiv.ofBijective (relationFunctionPullback g k h₁ h₂)
  constructor
  · intro s t h
    exact Subtype.ext (appTop_injective g (congrArg Subtype.val h))
  · intro s
    obtain ⟨v, hv, _⟩ := relationFunction_existsUnique g k h₁ h₂ H l hl₁ hl₂ s
    exact ⟨v, Subtype.ext hv⟩

/-- The comparison is the original source pullback, without chosen coordinates. -/
theorem relationFunctionRingEquiv_val (s : compatibleFunctions p q) :
    (relationFunctionRingEquiv g k h₁ h₂ H l hl₁ hl₂ s).val = g.appTop s.val := rfl

end FLT.Mazur.SchemeEffectiveEpiSections
