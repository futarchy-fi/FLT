/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafAffineTestCompatibility
public import FLT.Mazur.SheafPullbackQuotientNormalization

/-!
# Gluing comparisons of full ambient quotients

Local maps respecting a single global epimorphism are automatically compatible.
They glue uniquely, and local isomorphisms recover a global quotient isomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafQuotientComparisonGluing
open ModuleSheafOpenImmersionGluing SheafPullbackMapNormalization
universe u
variable {X : Scheme.{u}} {J : Type u} (Y : J → Scheme.{u})
  (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable {S Q P : X.Modules} (q : S ⟶ Q) [Epi q] (p : S ⟶ P)
variable (a : ∀ j, (pullback (i j)).obj Q ⟶ (pullback (i j)).obj P)
  (ha : ∀ j, (pullback (i j)).map q ≫ a j = (pullback (i j)).map p)
attribute [local irreducible] Scheme.Modules.pullback

include ha in
/-- The common epimorphism forces compatibility on all original overlaps. -/
theorem quotientComparison_compatible : Compatible Y i a := by
  apply compatible_of_affine_tests Y i a
  intro j k A l r d hl hr
  exact normalize_quotient_unique (i j) l d hl q p (i k) r hr (a j) (a k) (ha j) (ha k)

variable (hc : ∀ x : X, ∃ j, x ∈ Set.range (i j))

/-- Glue the actual local quotient comparisons without supplying overlap hypotheses. -/
@[irreducible] def quotientComparison : Q ⟶ P :=
  glue Y i hc a (quotientComparison_compatible Y i q p a ha)

/-- Every original local comparison is recovered exactly. -/
theorem quotientComparison_pullback (j : J) :
    (pullback (i j)).map (quotientComparison Y i q p a ha hc) = a j := by
  unfold quotientComparison
  exact pullback_glue Y i hc a (quotientComparison_compatible Y i q p a ha) j

/-- Gluing retains the full common ambient projection. -/
@[reassoc] theorem quotientComparison_projection :
    q ≫ quotientComparison Y i q p a ha hc = p := by
  apply ModuleSheafOpenImmersionGluing.hom_ext Y i hc
  intro j
  rw [Functor.map_comp, quotientComparison_pullback, ha j]

/-- The ambient epimorphism determines the global comparison uniquely. -/
theorem quotientComparison_unique (t : Q ⟶ P) (ht : q ≫ t = p) :
    t = quotientComparison Y i q p a ha hc := by
  apply (cancel_epi q).mp
  rw [ht, quotientComparison_projection]

/-- Local invertibility makes the constructed global quotient comparison invertible. -/
theorem quotientComparison_isIso (hiso : ∀ j, IsIso (a j)) :
    IsIso (quotientComparison Y i q p a ha hc) := by
  unfold quotientComparison
  exact glue_isIso Y i hc a (quotientComparison_compatible Y i q p a ha) hiso

/-- Recover the original global quotient up to its full ambient-compatible isomorphism. -/
@[irreducible] def quotientComparisonIso (hiso : ∀ j, IsIso (a j)) : Q ≅ P :=
  let _ := quotientComparison_isIso Y i q p a ha hc hiso
  asIso (quotientComparison Y i q p a ha hc)

/-- The constructed isomorphism recovers the whole original quotient projection. -/
@[reassoc] theorem quotientComparisonIso_projection (hiso : ∀ j, IsIso (a j)) :
    q ≫ (quotientComparisonIso Y i q p a ha hc hiso).hom = p := by
  unfold quotientComparisonIso
  exact quotientComparison_projection Y i q p a ha hc

end FLT.Mazur.ModuleSheafQuotientComparisonGluing
