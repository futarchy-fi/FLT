/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCoefficientModificationSections
public import FLT.Mazur.WeierstrassCoefficientShearRootChange

/-!
# Original arithmetic sections commute with whole-model coefficient transport

The actual section on each independently constructed coefficient model
specializes along the original coefficient map. Root changes retain that
same section, so the comparisons apply to arithmetic points themselves.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
  (r : S) (v : T) (j : ℕ) (hj : j ≤ n) (f : S →ₐ[A] T)
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap A S))
local notation "qT" => Spec.map (CommRingCat.ofHom (algebraMap A T))
local notation "b" => Spec.map (CommRingCat.ofHom f.toRingHom)

/-- Whole-model coefficient specialization is the restriction of the original arithmetic section. -/
@[reassoc] theorem e0CoefficientSection_specialization (P : ellipticE0 A W) :
    e0CoefficientSection A hπ data T v j hj P ≫
        coefficientShearSpecialization hπ data S T r v j hj f =
      b ≫ e0CoefficientSection A hπ data S r j hj P := by
  have hb : b ≫ qS = qT := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext f.commutes)
  apply (coefficientShearGlued_isPullback hπ data S r j hj).hom_ext
  · simp only [Category.assoc, coefficientShearSpecialization_structure,
      e0CoefficientSection_structure_assoc, e0CoefficientSection_structure,
      Category.comp_id]
  · rw [Category.assoc, coefficientShearSpecialization_projection,
      e0CoefficientSection_projection, Category.assoc, e0CoefficientSection_projection,
      ← Category.assoc, hb]

omit T [CommRing T] [Algebra A T] v f in
/-- Changing the coefficient root carries the original arithmetic section to its other formula. -/
@[reassoc] theorem e0CoefficientSection_rootChange (t : S) (P : ellipticE0 A W) :
    e0CoefficientSection A hπ data S r j hj P ≫
        (coefficientShearRootChange hπ data S r t j hj).hom =
      e0CoefficientSection A hπ data S t j hj P := by
  apply (coefficientShearGlued_isPullback hπ data S t j hj).hom_ext
  · rw [Category.assoc, coefficientShearRootChange_structure,
      e0CoefficientSection_structure, e0CoefficientSection_structure]
  · rw [Category.assoc, coefficientShearRootChange_projection,
      e0CoefficientSection_projection, e0CoefficientSection_projection]

end FLT.Mazur.WeierstrassDividedDepth
