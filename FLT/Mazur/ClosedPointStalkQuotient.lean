/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPointStalkMap

/-!
# Actual stalk quotient maps on composite germs

Composition and spectrum coefficients can be checked on abstract stalks
before specializing to large glued schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ClosedPointStalkMap

set_option backward.isDefEq.respectTransparency false

/-- A commuting stalk triangle also commutes on maximal-ideal power quotients. -/
theorem quotientMap_comp_mk {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y) (hy : f x = y)
    {r s : ℕ} (hrs : r ≤ s) {R : CommRingCat} (g : R ⟶ Y.presheaf.stalk y)
    (k : R ⟶ X.presheaf.stalk x) (h : g ≫ pointMap f x y hy = k) (a : R) :
    quotientMap f x y hy hrs (Ideal.Quotient.mk _ (g a)) = Ideal.Quotient.mk _ (k a) := by
  rw [quotientMap_mk]
  exact congrArg (fun l : R ⟶ X.presheaf.stalk x ↦ Ideal.Quotient.mk
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r) (l a)) h

/-- The spectrum stalk quotient map preserves the original ring coefficients. -/
theorem quotientMap_spec_mk {A B : CommRingCat} (φ : B ⟶ A)
    (x : Spec A) (y : Spec B) (hy : Spec.map φ x = y)
    {r s : ℕ} (hrs : r ≤ s) (b : B) :
    quotientMap (Spec.map φ) x y hy hrs (Ideal.Quotient.mk _ (StructureSheaf.toStalk B y b)) =
      Ideal.Quotient.mk _ (StructureSheaf.toStalk A x (φ b)) := by
  rw [quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (pointMap_spec φ x y hy b)

end FLT.Mazur.ClosedPointStalkMap
