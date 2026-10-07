/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCrossCoverOverlap
public import FLT.Mazur.SchemeDescentPairTransport

/-!
# Coherence of cross-cover comparisons on arbitrary triple charts

The product comparisons restrict to transport along the two actual maps into
the cover. Their cocycle follows from the original descent datum, with no
requirement that the covering charts coincide over the cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeCrossCoverOverlap
open SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y U V T : Scheme.{u}} (p : Y ⟶ X) (b : U ⟶ Y) (c : V ⟶ Y)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)

/-- Cross-cover comparison is transport along its two actual projections into the cover. -/
theorem transition_eq_transport : transition p b c D =
    D.transport (Limits.pullback.fst (b ≫ p) (c ≫ p) ≫ b)
      (Limits.pullback.snd (b ≫ p) (c ≫ p) ≫ c) (by
        simpa only [Category.assoc] using
          Limits.pullback.condition (f := b ≫ p) (g := c ≫ p)) := rfl

/-- Testing a cross-cover comparison recovers transport along the specified cover maps. -/
theorem transition_on_test (t : T ⟶ product p b c) (a d : T ⟶ Y)
    (ha : t ≫ (Limits.pullback.fst (b ≫ p) (c ≫ p) ≫ b) = a)
    (hd : t ≫ (Limits.pullback.snd (b ≫ p) (c ≫ p) ≫ c) = d)
    (w : a ≫ p = d ≫ p) :
    normalize _ _ t a d ha hd M (transition p b c D) = D.transport a d w := by
  rw [transition_eq_transport]
  exact D.transport_pullback _ _ _ t a d ha hd w

/-- All three cross-cover comparisons satisfy the cocycle on any compatible triple test. -/
theorem transition_cocycle {W : Scheme.{u}} (d : W ⟶ Y)
    (t12 : T ⟶ product p b c) (t23 : T ⟶ product p c d)
    (t13 : T ⟶ product p b d) (a1 a2 a3 : T ⟶ Y)
    (h12l : t12 ≫ (Limits.pullback.fst (b ≫ p) (c ≫ p) ≫ b) = a1)
    (h12r : t12 ≫ (Limits.pullback.snd (b ≫ p) (c ≫ p) ≫ c) = a2)
    (h23l : t23 ≫ (Limits.pullback.fst (c ≫ p) (d ≫ p) ≫ c) = a2)
    (h23r : t23 ≫ (Limits.pullback.snd (c ≫ p) (d ≫ p) ≫ d) = a3)
    (h13l : t13 ≫ (Limits.pullback.fst (b ≫ p) (d ≫ p) ≫ b) = a1)
    (h13r : t13 ≫ (Limits.pullback.snd (b ≫ p) (d ≫ p) ≫ d) = a3) :
    (normalize _ _ t12 a1 a2 h12l h12r M (transition p b c D)).hom ≫
        (normalize _ _ t23 a2 a3 h23l h23r M (transition p c d D)).hom =
      (normalize _ _ t13 a1 a3 h13l h13r M (transition p b d D)).hom := by
  have w12 : a1 ≫ p = a2 ≫ p := by
    rw [← h12l, ← h12r]
    simp only [Category.assoc]
    rw [Limits.pullback.condition]
  have w23 : a2 ≫ p = a3 ≫ p := by
    rw [← h23l, ← h23r]
    simp only [Category.assoc]
    rw [Limits.pullback.condition]
  rw [transition_on_test p b c D t12 a1 a2 h12l h12r w12,
    transition_on_test p c d D t23 a2 a3 h23l h23r w23,
    transition_on_test p b d D t13 a1 a3 h13l h13r (w12.trans w23)]
  exact D.transport_comp a1 a2 a3 w12 w23

end FLT.Mazur.SchemeCrossCoverOverlap
