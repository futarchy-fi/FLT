/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealObstructionOrientation
public import FLT.Mazur.IdealResidualFlatBaseChange

/-!
# The affine obstruction comparison for the actual tensor algebra

The ring inclusion into the tensor algebra is the module scalar-extension
unit. Consequently the original affine obstruction transition is exactly
the comparison in the presentation-free vanishing criterion.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.AffineObstructionBaseChange
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (S : Type*) [CommRing S] [Algebra R S]

/-- The original algebra maps into its actual scalar extension. -/
abbrev rightMap : A →+* S ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom

/-- The original algebra and the new base form the canonical commutative square. -/
theorem square : (rightMap (A := A) S).comp (algebraMap R A) =
    (algebraMap S (S ⊗[R] A)).comp (algebraMap R S) :=
  Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm

/-- The original affine transition is precisely the module-first tensor comparison. -/
theorem transition_eq (I : Ideal R) (z : A ⊗[R] I) :
    IdealTensorKernel.transition (algebraMap R S) (rightMap S) (square S) I z =
      TensorProduct.map (ScalarExtensionUnit.unit S A)
        (IdealTensorKernel.idealTransition (algebraMap R S) I) z := by
  induction z with
  | tmul a i => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Killing the original affine obstruction kills the entire new affine obstruction. -/
theorem inclusion_injective (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S) (rightMap S) (square S) I z.val = 0) :
    Function.Injective (FCurve.idealTensorInclusion (S := S ⊗[R] A)
      (I.map (algebraMap R S))) := by
  apply IdealObstructionOrientation.inclusion_injective (S := A) S I
  intro z
  rw [← transition_eq]
  exact h z

end FLT.Mazur.AffineObstructionBaseChange
