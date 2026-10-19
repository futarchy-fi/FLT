/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineComparisonCocycle
public import FLT.Mazur.CyclicCharacteristicAffineSubgroupOverlap

/-!
# Coherence of the concrete closed subgroup overlap maps

Monicity of the actual closed inclusions transfers the full comparison
identity and composition laws to the concrete subgroup schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] affineSubgroupOverlapMap affineComparisonOverlapMap
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
/-- Successive named refinements agree on the concrete closed subgroup schemes. -/
theorem affineSubgroupOverlapMap_comp :
    affineSubgroupOverlapMap n b c q' r' q'' r'' g hgq hgr ≫
      affineSubgroupOverlapMap n b c q r q' r' f hfq hfr =
    affineSubgroupOverlapMap n b c q r q'' r'' j hjq hjr := by
  apply (cancel_mono (affineSubgroupInclusion n b c q r)).mp
  simp only [Category.assoc, affineSubgroupOverlapMap_inclusion,
    affineSubgroupOverlapMap_inclusion_assoc]
  rw [affineComparisonOverlapMap_comp n b c q r q' r' q'' r'' f g j hj]

/-- Identity refinement is the identity of the actual closed subgroup scheme. -/
theorem affineSubgroupOverlapMap_id
    (hq : q = Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ q)
    (hr : r = Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ r) :
    affineSubgroupOverlapMap n b c q r q r (RingHom.id A) hq hr =
      𝟙 (affineSubgroupScheme n b c q r) := by
  apply (cancel_mono (affineSubgroupInclusion n b c q r)).mp
  rw [affineSubgroupOverlapMap_inclusion, affineComparisonOverlapMap_id,
    Category.comp_id, Category.id_comp]

end FLT.Mazur.CyclicCharacteristicAtlas
