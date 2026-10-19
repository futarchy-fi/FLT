/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupClassification

/-!
# The original full comparison detects the local closed subgroup locus

A given affine comparison parameter factors through the actual closed locus
exactly when its full original curve map extends compatibly to the subgroups.
The lift is unique and no Cartier generator is fixed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {A : Type} [CommRing A]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
  (B : Type) [CommRing B] [Algebra A B]
local notation "s" => affineComparisonStructure n b c q r
local notation "i" => affineSubgroupInclusion n b c q r
local notation "t" => Spec.algebraMap A B
local notation "H" => FiniteSubgroup.baseChange (normalizedSubgroup n b) (t ≫ q)
local notation "J" => FiniteSubgroup.baseChange (normalizedSubgroup n c) (t ≫ r)

/-- The local closed locus detects preservation of the full original normalized subgroups. -/
theorem affineSubgroupInclusion_factorization_iff
    (f : {f : Spec (.of B) ⟶ affineComparisonScheme n b c q r // f ≫ s = t}) :
    (∃ k : Spec (.of B) ⟶ affineSubgroupScheme n b c q r, k ≫ i = f.val) ↔
      ∃ a : CompatibleIso H J, a.curve = affineUniversalComparisonOnTest n b c q r B f := by
  constructor
  · rintro ⟨k, hk⟩
    have ht : k ≫ affineSubgroupStructure n b c q r = t := by
      change k ≫ i ≫ s = t
      rw [← Category.assoc, hk]
      exact f.property
    refine ⟨affineSubgroupPointEquiv n b c q r B ⟨k, ht⟩, ?_⟩
    rw [affineSubgroupPointEquiv_curve]
    congr 1
    exact Subtype.ext hk
  · rintro ⟨a, ha⟩
    let k := (affineSubgroupPointEquiv n b c q r B).symm a
    refine ⟨k.val, ?_⟩
    have hc := affineSubgroupPointEquiv_curve n b c q r B k
    rw [(affineSubgroupPointEquiv n b c q r B).apply_symm_apply a, ha] at hc
    have he : f = subgroupTestForget i s t k := by
      apply (affineComparisonPointEquiv n b c q r B).injective
      simpa only [affineComparisonPointEquiv_universal] using hc
    exact (congrArg Subtype.val he).symm

/-- Every prescribed original compatible comparison determines its unique closed-locus lift. -/
theorem affineSubgroupInclusion_factorization_unique
    (f : {f : Spec (.of B) ⟶ affineComparisonScheme n b c q r // f ≫ s = t})
    (a : CompatibleIso H J) (ha : a.curve = affineUniversalComparisonOnTest n b c q r B f) :
    ∃! k : Spec (.of B) ⟶ affineSubgroupScheme n b c q r, k ≫ i = f.val := by
  obtain ⟨k, hk⟩ := (affineSubgroupInclusion_factorization_iff n b c q r B f).mpr ⟨a, ha⟩
  exact ⟨k, hk, fun l hl ↦ (cancel_mono i).mp (hl.trans hk.symm)⟩

end FLT.Mazur.CyclicCharacteristicAtlas
