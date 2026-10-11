/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSectionIsoReconstruction
public import FLT.Mazur.ModulePushforwardTransitionCoherence

/-!
# Reconstructing sections along actual adic stage maps

Quotient comparisons preserving the adjunction units transport formal reconstruction
to the original stage pullbacks. Epimorphic projections force transition compatibility.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.IdealAdicQuotient

open FCurve

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (L : X.Modules) [L.IsFinitePresentation]
  (Y : ℕ → Scheme.{u}) (p : ∀ m, Y m ⟶ X)
  (r : ∀ {a b : ℕ}, a ≤ b → (Y a ⟶ Y b))
  (hr : ∀ a b (hab : a ≤ b), r hab ≫ p b = p a)
  (e : ∀ m, quotient I L (m + 1) ≅ (pushforward (p m)).obj ((pullback (p m)).obj L))
  (he : ∀ m, projection I L (m + 1) ≫ (e m).hom =
    (pullbackPushforwardAdjunction (p m)).unit.app L)

include he

/-- Preservation of the actual units forces compatibility with original stage transitions. -/
theorem quotientIso_original_transition {a b : ℕ} (hab : a ≤ b) :
    (e b).hom ≫ pushforwardSectionTransition (p a) (p b) (r hab) (hr a b hab)
        (pullbackStageIso (p a) (p b) (r hab) (hr a b hab) L).hom =
      reduction I L (Nat.add_le_add_right hab 1) ≫ (e a).hom := by
  apply (cancel_epi (projection I L (b + 1))).mp
  rw [← Category.assoc, he, ← Category.assoc, projection_reduction, he]
  exact unit_pushforwardSectionTransition _ _ _ _ L

/-- Original compatible stage sections reconstruct the unique complete section. -/
theorem existsUnique_section_original
    (hrec : ∀ q : ∀ m, Γ(quotient I L (m + 1), ⊤),
      (∀ a b (hab : a ≤ b),
        (reduction I L (Nat.add_le_add_right hab 1)).app ⊤ (q b) = q a) →
      ∃! t : Γ(L, ⊤), ∀ m, (projection I L (m + 1)).app ⊤ t = q m)
    (s : ∀ m, Γ((pullback (p m)).obj L, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (pullbackStageIso (p a) (p b) (r hab) (hr a b hab) L).hom.app ⊤
        (pullGlobal (r hab) _ (s b)) = s a) :
    ∃! t : Γ(L, ⊤), ∀ m, pullGlobal (p m) L t = s m := by
  exact existsUnique_section_of_quotient_iso I L
    (fun m ↦ (pushforward (p m)).obj ((pullback (p m)).obj L)) e
    (fun m ↦ (pullbackPushforwardAdjunction (p m)).unit.app L) he
    (fun {a b} hab ↦ pushforwardSectionTransition (p a) (p b) (r hab) (hr a b hab)
      (pullbackStageIso (p a) (p b) (r hab) (hr a b hab) L).hom)
    (fun _ _ hab ↦ quotientIso_original_transition I L Y p r hr e he hab)
    hrec s (fun a b hab ↦ (pushforwardSectionTransition_top (p a) (p b) (r hab)
      (hr a b hab) (pullbackStageIso (p a) (p b) (r hab) (hr a b hab) L).hom
      (s b)).trans (hs a b hab))

end FLT.Mazur.IdealAdicQuotient
