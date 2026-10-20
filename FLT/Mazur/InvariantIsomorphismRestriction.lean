/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantFunctorial
public import FLT.Mazur.IdealSheafClosedTransitions

/-!
# Full invariant and boundary coefficients under isomorphisms

An isomorphism on sources and an epimorphism on the entire relation identify
invariant rings. Exact boundary pullback along an isomorphism both preserves
and reflects the full boundary equation, without reducing its ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationInvariantSpectrum
open SchemeEffectiveEpiSections
variable {E A E' A' : Scheme.{0}} (p q : E ⟶ A) (p' q' : E' ⟶ A')
  (u : A' ⟶ A) (v : E' ⟶ E) (hp : v ≫ p = p' ≫ u) (hq : v ≫ q = q' ≫ u)

/-- Genuine source isomorphisms identify full invariants when all arrows are detected. -/
theorem relationPullback_bijective_of_isIso [IsIso u] [Epi v] :
    Function.Bijective (relationPullback p q p' q' u v hp hq) := by
  refine ⟨relationPullback_injective p q p' q' u v hp hq, fun s ↦ ?_⟩
  let z := (inv u).appTop s.val
  have hu : u.appTop z = s.val := by
    change (u ≫ inv u).appTop s.val = s.val
    rw [IsIso.hom_inv_id]
    rfl
  have hz : p.appTop z = q.appTop z := by
    apply appTop_injective v
    change (v ≫ p).appTop z = (v ≫ q).appTop z
    rw [hp, hq, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    change p'.appTop (u.appTop z) = q'.appTop (u.appTop z)
    rw [hu]
    exact s.property
  exact ⟨⟨z, hz⟩, Subtype.ext hu⟩

end FLT.Mazur.SchemeRelationInvariantSpectrum

namespace FLT.Mazur.IdealSheafClosedTransitions
variable {X Y : Scheme.{0}} (I : X.IdealSheafData) (J : Y.IdealSheafData)
  (a : X ⟶ Y) (h : J.comap a = I)

/-- An unchanged boundary over an isomorphic source has an isomorphic transition. -/
theorem map_isIso [IsIso a] : IsIso (map I J a h) :=
  (isPullback I J a h).isIso_snd_of_isIso

include h in
/-- Boundary vanishing is reflected, not only preserved, by a source isomorphism. -/
theorem section_zero_iff_of_isIso [IsIso a] (s : Γ(Y, ⊤)) :
    I.subschemeι.appTop (a.appTop s) = 0 ↔ J.subschemeι.appTop s = 0 := by
  let _ := map_isIso I J a h
  rw [section_square]
  exact (map_eq_zero_iff _ (SchemeEffectiveEpiSections.appTop_injective (map I J a h)))

end FLT.Mazur.IdealSheafClosedTransitions
