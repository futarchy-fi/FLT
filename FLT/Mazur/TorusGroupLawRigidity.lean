/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentNormalizedMorphism
public import FLT.Mazur.LaurentPairProduct

/-!
# A pointed torus presentation determines the original group law

Over a domain, the unit laws alone determine a multiplication on the torus.
Consequently a pointed scheme isomorphism to an independently given monoid
preserves its original multiplication. No compatibility is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.TorusGroupLawRigidity
open LaurentPairProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
local notation "G" => MultiplicativeGroupScheme.gm R
local notation "L" => R[T;T⁻¹]
local notation "D" => R[T;T⁻¹][T;T⁻¹]

omit [IsDomain R] in
/-- An actual torus product map retains the base of the double Laurent chart. -/
theorem productMap_base (m : (G) ⊗ (G) ⟶ (G)) :
    ((productIso R).hom ≫ m.left) ≫ (G).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
  rw [Category.assoc, m.w]
  change (productIso R).hom ≫ (fst (G) (G)).left ≫ (G).hom = _
  rw [productIso_fst_assoc]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The unit laws uniquely determine multiplication on the original torus scheme. -/
theorem multiplication_unique (m : (G) ⊗ (G) ⟶ (G))
    (hl : η[(G)] ▷ (G) ≫ m = (λ_ (G)).hom)
    (hr : (G) ◁ η[(G)] ≫ m = (ρ_ (G)).hom) : m = μ[(G)] := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (productIso R).hom).mp
  apply LaurentNormalizedMorphism.hom_ext _ _ (productMap_base m) (productMap_base μ[(G)])
  · rw [← Category.assoc, firstUnit_productIso]
    change (((λ_ (G)).inv ≫ η[(G)] ▷ (G)) ≫ m).left = _
    rw [Category.assoc, hl, Iso.inv_hom_id]
    rfl
  · rw [← Category.assoc, secondUnit_productIso]
    change (((ρ_ (G)).inv ≫ (G) ◁ η[(G)]) ≫ m).left = _
    rw [Category.assoc, hr, Iso.inv_hom_id]
    rfl
  · rw [← Category.assoc, firstUnit_productIso]
    change (((λ_ (G)).inv ≫ η[(G)] ▷ (G)) ≫ μ[(G)]).left = _
    rw [Category.assoc, MonObj.one_mul, Iso.inv_hom_id]
    rfl
  · rw [← Category.assoc, secondUnit_productIso]
    change (((ρ_ (G)).inv ≫ (G) ◁ η[(G)]) ≫ μ[(G)]).left = _
    rw [Category.assoc, MonObj.mul_one, Iso.inv_hom_id]
    rfl

/-- A pointed torus scheme presentation preserves any pre-existing monoid law. -/
theorem isMonHom_of_pointedIso {X : Over (Spec (.of R))} [MonObj X]
    (e : (G) ≅ X) (he : η[(G)] ≫ e.hom = η[X]) : IsMonHom e.hom := by
  have hm : (e.hom ⊗ₘ e.hom) ≫ μ[X] ≫ e.inv = μ[(G)] := by
    apply multiplication_unique
    · rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, he, one_mul_hom_assoc]
      simp
    · rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, he, mul_one_hom_assoc]
      simp
  refine ⟨he, ?_⟩
  apply (cancel_mono e.inv).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hm.symm

end FLT.Mazur.TorusGroupLawRigidity
