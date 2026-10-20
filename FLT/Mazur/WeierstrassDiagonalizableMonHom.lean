/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableProductScheme
public import FLT.Mazur.MultiplicativeGroupObjectHom
public import FLT.Mazur.WeierstrassDiagonalizableLiftUniqueness

/-!
# Corrected diagonalizable maps are actual group-scheme homomorphisms

The full coface equation is equivalent to the categorical multiplication
square. Cancellation proves identity preservation, so the constructed
corrections carry the original `IsMonHom` structure.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open WeierstrassIntegralChart DiagonalizableCobar CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] productOverIso productSchemeIso productEquiv

universe u
variable {R G : Type u} [CommRing R] [AddCommMonoid G] (W : WeierstrassCurve R)

/-- The full coface defect vanishes precisely for the original monoid-scheme morphisms. -/
theorem defect_eq_one_iff_isMonHom (p : Points W (AddMonoidAlgebra R G)) :
    defect W p = 1 ↔ IsMonHom p := by
  have hm : defect W p = 1 ↔ μ[model R G] ≫ p = (p ⊗ₘ p) ≫ μ[(integralSmoothGroup W).X] := by
    rw [← cancel_epi (productOverIso R G).hom]
    rw [← Category.assoc, productOverIso_mul]
    have he : (productOverIso R G).hom ≫ (p ⊗ₘ p) =
        lift (smoothAlgebraTestMap (firstMap R G) ≫ p)
          (smoothAlgebraTestMap (secondMap R G) ≫ p) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp only [Category.assoc, tensorHom_fst, tensorHom_snd, lift_fst, lift_snd,
          productOverIso_fst_assoc, productOverIso_snd_assoc]
    rw [← Category.assoc, he, ← Hom.mul_def]
    change _ ↔ smoothAlgebraReduction W (diagonalMap R G) p =
      smoothAlgebraReduction W (firstMap R G) p * smoothAlgebraReduction W (secondMap R G) p
    rw [defect_base, div_eq_one, eq_comm]
  exact hm.trans ⟨MultiplicativeGroupObjectHom.isMonHom p, fun h => h.mul_hom⟩

/-- The actual correction preserves both multiplication and the identity. -/
theorem corrected_isMonHom (I : Ideal R) (hI : I ^ 2 = ⊥)
    (p : Points W (AddMonoidAlgebra R G))
    (hp : defect W (smoothAlgebraReduction W (coefficientReduction R G I) p) = 1) :
    IsMonHom (corrected W I hI p hp) :=
  (defect_eq_one_iff_isMonHom W _).mp (corrected_defect W I hI p hp)

end FLT.Mazur.WeierstrassDiagonalizableDefect
