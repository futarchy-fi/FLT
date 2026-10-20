/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCharacterAdicMapExt
public import FLT.Mazur.FiniteCharacterAdicJacobson
public import FLT.Mazur.JacobsonReductionOpenDetection
public import FLT.Mazur.DiagonalizableCoefficientReduction

/-!
# Detecting maps into a scheme from their original character reductions

If the initial image lies in one specified affine chart of the target, the
Jacobson criterion puts the whole image in that chart. Affine coefficient
separatedness then detects equality of the original scheme morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteCharacterAdicElements

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G C : Type} [CommRing R] [AddCommMonoid G] [Finite G] [CommRing C]
  (I : Ideal R) [IsAdicComplete I R]

/-- Initial reduction detects landing in any specified open of the original target. -/
theorem range_subset_of_reduction {X : Scheme}
    (q : Spec (.of (AddMonoidAlgebra R G)) ⟶ X) (U : X.Opens)
    (h : Set.range (Spec.map (CommRingCat.ofHom (reduction (G := G) I 0)) ≫ q) ⊆ U) :
    Set.range q ⊆ U := by
  apply JacobsonReductionOpenDetection.range_subset (reduction (G := G) I 0)
    (DiagonalizableCobar.coefficientReduction_surjective R G (I ^ (0 + 1)))
    (reduction_zero_ker_le_jacobson I) q U
  exact h

/-- A specified initial affine chart suffices to detect equality in the entire target scheme. -/
theorem schemeMap_ext_of_chart {X : Scheme} (i : Spec (.of C) ⟶ X) [IsOpenImmersion i]
    {f g : Spec (.of (AddMonoidAlgebra R G)) ⟶ X}
    (hi : Set.range (Spec.map (CommRingCat.ofHom (reduction (G := G) I 0)) ≫ f) ⊆
      Set.range i)
    (h : ∀ m, Spec.map (CommRingCat.ofHom (reduction (G := G) I m)) ≫ f =
      Spec.map (CommRingCat.ofHom (reduction (G := G) I m)) ≫ g) : f = g := by
  have hf : Set.range f ⊆ Set.range i := range_subset_of_reduction I f i.opensRange hi
  have hg : Set.range g ⊆ Set.range i := range_subset_of_reduction I g i.opensRange (by
    rw [← h 0]
    exact hi)
  let a := IsOpenImmersion.lift i f hf
  let b := IsOpenImmersion.lift i g hg
  have ha : a ≫ i = f := IsOpenImmersion.lift_fac i f hf
  have hb : b ≫ i = g := IsOpenImmersion.lift_fac i g hg
  have hab : a = b := by
    apply specMap_ext I
    intro m
    apply (cancel_mono i).mp
    rw [Category.assoc, Category.assoc, ha, hb, h m]
  rw [← ha, ← hb, hab]

end FLT.Mazur.FiniteCharacterAdicElements
