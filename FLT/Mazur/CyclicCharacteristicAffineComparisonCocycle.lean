/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineComparisonOverlap
public import FLT.Mazur.WeierstrassComparisonCoefficientComposition

/-!
# Double and triple coherence of actual affine comparison overlaps

The constructed overlap maps compose exactly, including separately named
coefficient and chart maps. Thus the full comparison parameters have no
choice-dependent discrepancy on triple affine refinements.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] comparisonPresentationHom
variable (n : ℕ) [NeZero n] {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
  (q' : Spec (.of B) ⟶ normalizedLocus n b) (r' : Spec (.of B) ⟶ normalizedLocus n c)
  (q'' : Spec (.of C) ⟶ normalizedLocus n b) (r'' : Spec (.of C) ⟶ normalizedLocus n c)
  (f : A →+* B) (g : B →+* C) (j : A →+* C) (hj : j = g.comp f)
  (hfq : q' = Spec.map (CommRingCat.ofHom f) ≫ q)
  (hfr : r' = Spec.map (CommRingCat.ofHom f) ≫ r)
  (hgq : q'' = Spec.map (CommRingCat.ofHom g) ≫ q')
  (hgr : r'' = Spec.map (CommRingCat.ofHom g) ≫ r')
  (hjq : q'' = Spec.map (CommRingCat.ofHom j) ≫ q)
  (hjr : r'' = Spec.map (CommRingCat.ofHom j) ≫ r)

include hj in
/-- Direct and iterated actual comparison overlaps agree on every full parameter. -/
theorem affineComparisonOverlapMap_comp :
    affineComparisonOverlapMap n b c q' r' q'' r'' g hgq hgr ≫
      affineComparisonOverlapMap n b c q r q' r' f hfq hfr =
    affineComparisonOverlapMap n b c q r q'' r'' j hjq hjr := by
  rw [affineComparisonOverlapMap_eq_spec, affineComparisonOverlapMap_eq_spec,
    affineComparisonOverlapMap_eq_spec, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (comparisonPresentationHom_comp
    (affineEquation n b q) (affineEquation n c r)
    (affineEquation n b q') (affineEquation n c r')
    (affineEquation n b q'') (affineEquation n c r'') f g j hj _ _ _ _ _ _)

/-- Identity refinement acts identically on the actual affine comparison scheme. -/
theorem affineComparisonOverlapMap_id
    (hq : q = Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ q)
    (hr : r = Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ r) :
    affineComparisonOverlapMap n b c q r q r (RingHom.id A) hq hr =
      𝟙 (affineComparisonScheme n b c q r) := by
  rw [affineComparisonOverlapMap_eq_spec, comparisonPresentationHom_id]
  exact Spec.map_id _

end FLT.Mazur.CyclicCharacteristicAtlas
