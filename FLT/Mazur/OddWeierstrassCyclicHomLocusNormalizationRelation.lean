/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomLocusRelabelNormalization
public import FLT.Mazur.OddWeierstrassCyclicHomMarkedFamilyRelation

/-!
# The actual subgroup normalization relation represents original marked comparisons

The kernel pair retains both original subgroup parameters. Its test points
are exactly pairs admitting original marked comparisons on every affine test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual kernel pair of normalization on the closed subgroup locus. -/
def cyclicHomLocusNormalizationRelation : Scheme :=
  pullback (cyclicHomLocusNormalization n) (cyclicHomLocusNormalization n)

/-- The first original subgroup parameter in the represented relation. -/
def cyclicHomLocusRelationFirst :
    cyclicHomLocusNormalizationRelation n ⟶ cyclicHomUniversalMultiplicationLocus n :=
  pullback.fst _ _

/-- The second original subgroup parameter in the represented relation. -/
def cyclicHomLocusRelationSecond :
    cyclicHomLocusNormalizationRelation n ⟶ cyclicHomUniversalMultiplicationLocus n :=
  pullback.snd _ _

/-- The actual relation equates the full normalized closed-locus parameters. -/
@[reassoc] theorem cyclicHomLocusRelation_condition :
    cyclicHomLocusRelationFirst n ≫ cyclicHomLocusNormalization n =
      cyclicHomLocusRelationSecond n ≫ cyclicHomLocusNormalization n := pullback.condition

/-- Closed-locus normalization equality is equality of the complete normalized parameters. -/
theorem cyclicHomLocusNormalization_eq_iff {T : Scheme}
    (f g : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    f ≫ cyclicHomLocusNormalization n = g ≫ cyclicHomLocusNormalization n ↔
      cyclicHomNormalizedPoint n (f ≫ cyclicHomUniversalMultiplicationLocusInclusion n) =
        cyclicHomNormalizedPoint n (g ≫ cyclicHomUniversalMultiplicationLocusInclusion n) := by
  rw [← cancel_mono (cyclicHomNormalizedLocusInclusion n),
    ← cancel_mono (cyclicHomUniversalMultiplicationLocusInclusion n)]
  simp only [Category.assoc, cyclicHomLocusNormalization_parameter]

/-- Every pair with equal full normalized parameters gives an actual kernel-pair point. -/
def cyclicHomLocusRelationPoint {T : Scheme}
    (f g : T ⟶ cyclicHomUniversalMultiplicationLocus n)
    (h : f ≫ cyclicHomLocusNormalization n = g ≫ cyclicHomLocusNormalization n) :
    T ⟶ cyclicHomLocusNormalizationRelation n := pullback.lift f g h

/-- The actual relation retains the first original subgroup exactly. -/
@[reassoc] theorem cyclicHomLocusRelationPoint_first {T : Scheme}
    (f g : T ⟶ cyclicHomUniversalMultiplicationLocus n)
    (h : f ≫ cyclicHomLocusNormalization n = g ≫ cyclicHomLocusNormalization n) :
    cyclicHomLocusRelationPoint n f g h ≫ cyclicHomLocusRelationFirst n = f :=
  pullback.lift_fst _ _ _

/-- The actual relation retains the second original subgroup exactly. -/
@[reassoc] theorem cyclicHomLocusRelationPoint_second {T : Scheme}
    (f g : T ⟶ cyclicHomUniversalMultiplicationLocus n)
    (h : f ≫ cyclicHomLocusNormalization n = g ≫ cyclicHomLocusNormalization n) :
    cyclicHomLocusRelationPoint n f g h ≫ cyclicHomLocusRelationSecond n = g :=
  pullback.lift_snd _ _ _

/-- Two original subgroup parameters uniquely determine the relation point. -/
theorem cyclicHomLocusRelation_hom_ext {T : Scheme}
    (f g : T ⟶ cyclicHomLocusNormalizationRelation n)
    (h₁ : f ≫ cyclicHomLocusRelationFirst n = g ≫ cyclicHomLocusRelationFirst n)
    (h₂ : f ≫ cyclicHomLocusRelationSecond n = g ≫ cyclicHomLocusRelationSecond n) : f = g :=
  pullback.hom_ext h₁ h₂

/-- Original marked affine-test comparisons are precisely normalization-relation membership. -/
theorem cyclicHomLocusRelation_iff_affine_tests {T : Scheme}
    (f g : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    f ≫ cyclicHomLocusNormalization n = g ≫ cyclicHomLocusNormalization n ↔
      ∀ (R : Type) [CommRing R] (k : Spec (.of R) ⟶ T),
        CyclicHomMarkedFamilyRelated n
          (k ≫ (f ≫ cyclicHomUniversalMultiplicationLocusInclusion n))
          (k ≫ (g ≫ cyclicHomUniversalMultiplicationLocusInclusion n)) := by
  rw [cyclicHomLocusNormalization_eq_iff, cyclicHom_affineTests_iff_normalized_eq]

end FLT.Mazur.OddWeierstrassParameter
