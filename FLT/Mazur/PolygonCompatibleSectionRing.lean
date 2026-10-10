/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSectionRingFunctor

/-!
# Compatible systems of actual polygon sections

This is the ring of compatible sections of the constructed infinitesimal
system. No scheme limit, lifting theorem, or finite generation is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- The subring of actual sections compatible with every infinitesimal stage map. -/
def compatibleSectionRing : Subring (∀ m, boundaryGradedSections R n h m) where
  carrier := {s | ∀ {a b : ℕ} (f : a ⟶ b), boundarySectionsMap R n h f (s b) = s a}
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

/-- Projection to an original infinitesimal boundary section ring. -/
def compatibleSectionEval (m : ℕ) :
    compatibleSectionRing R n h →+* boundaryGradedSections R n h m :=
  (Pi.evalRingHom _ m).comp (compatibleSectionRing R n h).subtype

/-- Evaluation retains the specified stage transition maps. -/
theorem compatibleSectionEval_transition {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap R n h f).comp (compatibleSectionEval R n h b) =
      compatibleSectionEval R n h a := by
  apply RingHom.ext
  intro s
  exact s.property f

/-- Compatible ring maps into all actual stages assemble into the compatible-section ring. -/
def compatibleSectionLift {A : Type*} [NonAssocSemiring A]
    (e : ∀ m, A →+* boundaryGradedSections R n h m)
    (he : ∀ {a b : ℕ} (f : a ⟶ b), (boundarySectionsMap R n h f).comp (e b) = e a) :
    A →+* compatibleSectionRing R n h where
  toFun s := ⟨fun m ↦ e m s, fun f ↦ DFunLike.congr_fun (he f) s⟩
  map_zero' := Subtype.ext (funext fun m ↦ (e m).map_zero)
  map_one' := Subtype.ext (funext fun m ↦ (e m).map_one)
  map_add' s t := Subtype.ext (funext fun m ↦ (e m).map_add s t)
  map_mul' s t := Subtype.ext (funext fun m ↦ (e m).map_mul s t)

/-- The assembled ring map has precisely the given stage projections. -/
theorem compatibleSectionLift_eval {A : Type*} [NonAssocSemiring A]
    (e : ∀ m, A →+* boundaryGradedSections R n h m)
    (he : ∀ {a b : ℕ} (f : a ⟶ b), (boundarySectionsMap R n h f).comp (e b) = e a)
    (m : ℕ) :
    (compatibleSectionEval R n h m).comp (compatibleSectionLift R n h e he) = e m := rfl

/-- The projections jointly determine a compatible section. -/
theorem compatibleSection_ext {s t : compatibleSectionRing R n h}
    (he : ∀ m, compatibleSectionEval R n h m s = compatibleSectionEval R n h m t) : s = t :=
  Subtype.ext (funext he)

end FLT.Mazur.PolygonInfinitesimalStages
