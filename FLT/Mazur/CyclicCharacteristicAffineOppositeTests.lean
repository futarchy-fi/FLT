/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOppositeDescent

/-!
# Affine opposite reconstruction on arbitrary comparison tests

The reconstructed morphism has the required value on every test compatible
with a parameter in the original chart. Equality is detected on the actual
pullback fppf cover, so this retains scheme-theoretic comparison data.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] affineOppositeTarget affineOppositeDescend
variable (n : ℕ) [NeZero n] (b : Bool)
  (j : (invariantAffineCover n (!b)).I₀) {Y : Scheme}
  (f : invariantAffineChart n ⟨!b, j⟩ ⟶ Y)
  (hf : affineResidualSource n ⟨!b, j⟩ ≫ f = affineResidualTarget n ⟨!b, j⟩ ≫ f)

/-- Reconstructed invariants agree with every original-chart parameter related to the test. -/
theorem affineOppositeDescend_on_test {T : Scheme}
    (p : T ⟶ (affineOppositeOpen n b j).toScheme) (q : T ⟶ invariantAffineChart n ⟨!b, j⟩)
    (h : UnmarkedRelated n b (!b) (p ≫ (affineOppositeOpen n b j).ι)
      (q ≫ invariantAffineInclusion n ⟨!b, j⟩)) :
    p ≫ affineOppositeDescend n b j f hf = q ≫ f := by
  apply SchemeFppfFamily.cover_hom_ext ((affineOppositeCover n b j).pullback₁ p)
  intro i
  let l := pullback.fst p ((affineOppositeCover n b j).f i)
  let r := pullback.snd p ((affineOppositeCover n b j).f i)
  have hi := UnmarkedRelated.baseChange n (affineOppositeCover_related n b j i) r
  have hp : r ≫ (affineOppositeCover n b j).f i ≫ (affineOppositeOpen n b j).ι =
      l ≫ p ≫ (affineOppositeOpen n b j).ι := by
    rw [← Category.assoc, ← pullback.condition]
    simp only [Category.assoc, l]
  rw [hp] at hi
  have ht := UnmarkedRelated.baseChange n h l
  have he := affineResidual_invariant_on_test n ⟨!b, j⟩ f hf
    (r ≫ affineOppositeTarget n b j i) (l ≫ q)
    (by simpa only [Category.assoc] using UnmarkedRelated.trans n hi ht)
  change l ≫ p ≫ affineOppositeDescend n b j f hf = l ≫ q ≫ f
  rw [← Category.assoc, pullback.condition, Category.assoc,
    affineOppositeDescend_fac]
  simpa only [Category.assoc] using he

/-- The reconstructed map retains every same-chart comparison on the opposite overlap. -/
theorem affineOppositeDescend_invariant {T : Scheme}
    (p q : T ⟶ (affineOppositeOpen n b j).toScheme)
    (h : UnmarkedRelated n b b
      (p ≫ (affineOppositeOpen n b j).ι) (q ≫ (affineOppositeOpen n b j).ι)) :
    p ≫ affineOppositeDescend n b j f hf =
      q ≫ affineOppositeDescend n b j f hf := by
  apply SchemeFppfFamily.cover_hom_ext ((affineOppositeCover n b j).pullback₁ p)
  intro i
  let l := pullback.fst p ((affineOppositeCover n b j).f i)
  let r := pullback.snd p ((affineOppositeCover n b j).f i)
  have hi := UnmarkedRelated.baseChange n (affineOppositeCover_related n b j i) r
  have hp : r ≫ (affineOppositeCover n b j).f i ≫ (affineOppositeOpen n b j).ι =
      l ≫ p ≫ (affineOppositeOpen n b j).ι := by
    rw [← Category.assoc, ← pullback.condition]
    simp only [Category.assoc, l]
  rw [hp] at hi
  have ht := UnmarkedRelated.trans n hi (UnmarkedRelated.baseChange n h l)
  have he := affineOppositeDescend_on_test n b j f hf (l ≫ q)
    (r ≫ affineOppositeTarget n b j i) (by
      simpa only [Category.assoc] using UnmarkedRelated.symm n ht)
  change l ≫ p ≫ affineOppositeDescend n b j f hf =
    l ≫ q ≫ affineOppositeDescend n b j f hf
  rw [← Category.assoc, pullback.condition, Category.assoc,
    affineOppositeDescend_fac]
  simpa only [Category.assoc] using he.symm

/-- Reconstruction commutes with postcomposition of the original invariant morphism. -/
@[reassoc] theorem affineOppositeDescend_comp {Z : Scheme} (g : Y ⟶ Z) :
    affineOppositeDescend n b j f hf ≫ g =
      affineOppositeDescend n b j (f ≫ g) (by simp only [← Category.assoc, hf]) := by
  apply affineOppositeDescend_unique
  intro i
  rw [← Category.assoc, affineOppositeDescend_fac, Category.assoc]

end FLT.Mazur.CyclicCharacteristicOrbit
