/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSectionFunctor

/-!
# Compatible systems of actual polygon sections

This is the ring of compatible sections of the constructed arithmetic
system. No scheme limit, lifting theorem, or finite generation is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- The subring of actual sections compatible with every arithmetic stage map. -/
def compatibleSectionRing : Subring (∀ m, boundaryGradedSections A π n h m) where
  carrier := {s | ∀ {a b : ℕ} (f : a ⟶ b), boundarySectionsMap A π n h f (s b) = s a}
  zero_mem' := by intro a b f; exact map_zero _
  one_mem' := by intro a b f; exact map_one _
  add_mem' := by
    intro s t hs ht a b f
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (hs f) (ht f))
  mul_mem' := by
    intro s t hs ht a b f
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (hs f) (ht f))
  neg_mem' := by
    intro s hs a b f
    exact (map_neg _ _).trans (congrArg Neg.neg (hs f))

/-- Projection to an original arithmetic boundary section ring. -/
def compatibleSectionEval (m : ℕ) :
    compatibleSectionRing A π n h →+* boundaryGradedSections A π n h m :=
  (Pi.evalRingHom _ m).comp (compatibleSectionRing A π n h).subtype

/-- Evaluation retains the specified stage transition maps. -/
theorem compatibleSectionEval_transition {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap A π n h f).comp (compatibleSectionEval A π n h b) =
      compatibleSectionEval A π n h a := by
  apply RingHom.ext
  intro s
  exact s.property f

/-- Compatible ring maps into all actual stages assemble into the compatible-section ring. -/
def compatibleSectionLift {B : Type*} [NonAssocSemiring B]
    (e : ∀ m, B →+* boundaryGradedSections A π n h m)
    (he : ∀ {a b : ℕ} (f : a ⟶ b), (boundarySectionsMap A π n h f).comp (e b) = e a) :
    B →+* compatibleSectionRing A π n h where
  toFun s := ⟨fun m ↦ e m s, fun f ↦ DFunLike.congr_fun (he f) s⟩
  map_zero' := Subtype.ext (funext fun m ↦ (e m).map_zero)
  map_one' := Subtype.ext (funext fun m ↦ (e m).map_one)
  map_add' s t := Subtype.ext (funext fun m ↦ (e m).map_add s t)
  map_mul' s t := Subtype.ext (funext fun m ↦ (e m).map_mul s t)

/-- The assembled ring map has precisely the given stage projections. -/
theorem compatibleSectionLift_eval {B : Type*} [NonAssocSemiring B]
    (e : ∀ m, B →+* boundaryGradedSections A π n h m)
    (he : ∀ {a b : ℕ} (f : a ⟶ b), (boundarySectionsMap A π n h f).comp (e b) = e a)
    (m : ℕ) :
    (compatibleSectionEval A π n h m).comp (compatibleSectionLift A π n h e he) = e m := rfl

/-- The projections jointly determine a compatible section. -/
theorem compatibleSection_ext {s t : compatibleSectionRing A π n h}
    (he : ∀ m, compatibleSectionEval A π n h m s = compatibleSectionEval A π n h m t) : s = t :=
  Subtype.ext (funext he)

end FLT.Mazur.PolygonArithmeticStages
