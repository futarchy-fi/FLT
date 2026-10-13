/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationPrincipalLocalization
public import FLT.Mazur.SchemeRelationInvariantRestriction

/-!
# Localized invariants of the full geometric relation restriction

The localized coefficient ring is the invariant ring of the actual double
pullback relation on the principal source. Every original arrow with both
endpoints in that source is retained. The comparison preserves the original
structure-sheaf restriction, not just the abstract ring isomorphism type.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationPrincipalLocalization
open SchemeEffectiveEpiSections SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A) (s : compatibleFunctions p q)
  [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace D] [QuasiSeparatedSpace D]
local notation "W" => A.basicOpen s.val
local notation "hW" => compatibleFunctions_basicOpen p q s

/-- Localized full invariants are the exact invariants of the entire double restriction. -/
def fullEquiv : Localization.Away s ≃+*
    compatibleFunctions (fst p q (W).ι) (snd p q (W).ι) :=
  (openEquiv p q s).trans ((relationOpenCoordinates p q W hW).trans
    (invariantFunctionEquiv p q W hW))

/-- The full-relation comparison keeps the original open-subscheme section coordinates. -/
theorem fullEquiv_val (z : Localization.Away s) :
    (fullEquiv p q s z).val = (W).topIso.inv (openEquiv p q s z).val := rfl

/-- Each original coefficient maps by the actual principal open immersion. -/
theorem fullEquiv_algebraMap (a : compatibleFunctions p q) :
    (fullEquiv p q s (algebraMap _ (Localization.Away s) a)).val =
      (W).ι.appTop a.val := by
  rw [fullEquiv_val, openEquiv_algebraMap]
  change (A.presheaf.map _ ≫ (W).topIso.inv) a.val = (W).ι.appTop a.val
  simp only [Scheme.Opens.topIso_inv, ← Functor.map_comp, Scheme.Opens.ι_appTop]
  rfl

/-- The original localized invariant coefficient is uniquely recovered from every full solution. -/
theorem full_existsUnique
    (z : compatibleFunctions (fst p q (W).ι) (snd p q (W).ι)) :
    ∃! a : Localization.Away s, fullEquiv p q s a = z :=
  (fullEquiv p q s).bijective.existsUnique z

end FLT.Mazur.SchemeRelationPrincipalLocalization
