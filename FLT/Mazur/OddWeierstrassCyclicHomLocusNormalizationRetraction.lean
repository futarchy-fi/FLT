/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationNaturality
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedLocus

/-!
# Natural normalization retracts the actual subgroup locus

The complete normalized parameter is natural on arbitrary test schemes.
Uniqueness of both closed immersions gives naturality of its locus lift and
the retraction onto the actual normalized subgroup locus.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual closed normalized subgroup parameter is natural under every source map. -/
theorem cyclicHomNormalizedLocusPoint_natural {T U : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomMultiplicationEquation n f = 0) (k : U ⟶ T) :
    cyclicHomNormalizedLocusPoint n (k ≫ f)
      (cyclicHomMultiplicationEquation_zero_comp n f k h) =
        k ≫ cyclicHomNormalizedLocusPoint n f h := by
  apply (cancel_mono (cyclicHomNormalizedLocusInclusion n)).mp
  apply (cancel_mono (cyclicHomUniversalMultiplicationLocusInclusion n)).mp
  simp only [Category.assoc, cyclicHomNormalizedLocusPoint_parameter]
  exact cyclicHomNormalizedPoint_natural n f k

/-- Normalization is an actual morphism from the full subgroup locus to its closed slice. -/
def cyclicHomLocusNormalization :
    cyclicHomUniversalMultiplicationLocus n ⟶ cyclicHomNormalizedLocus n :=
  cyclicHomNormalizedLocusPoint n (cyclicHomUniversalMultiplicationLocusInclusion n)
    (cyclicHomUniversalLocus_equation_zero n)

/-- The global normalization morphism represents independently normalized test parameters. -/
theorem cyclicHomLocusNormalization_comp {T : Scheme}
    (q : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    q ≫ cyclicHomLocusNormalization n =
      cyclicHomNormalizedLocusPoint n (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)
        (cyclicHomMultiplicationEquation_zero_comp n _ q
          (cyclicHomUniversalLocus_equation_zero n)) :=
  (cyclicHomNormalizedLocusPoint_natural n _ (cyclicHomUniversalLocus_equation_zero n) q).symm

/-- Every point of the closed normalized subgroup locus has its auxiliary frame normalized. -/
theorem cyclicHomNormalizedLocus_satisfies {T : Scheme}
    (q : T ⟶ cyclicHomNormalizedLocus n) :
    SatisfiesNormalization (cyclicHomAuxiliaryPoint n
      (q ≫ cyclicHomNormalizedLocusInclusion n ≫
        cyclicHomUniversalMultiplicationLocusInclusion n)).appTop.hom := by
  have hs : cyclicHomNormalizedLocusInclusion n ≫
      cyclicHomUniversalMultiplicationLocusInclusion n ≫ (cyclicHomAuxiliary n).left =
        pullback.snd _ _ ≫ normalizedSliceInclusion := pullback.condition
  change SatisfiesNormalization (((q ≫ cyclicHomNormalizedLocusInclusion n ≫
    cyclicHomUniversalMultiplicationLocusInclusion n) ≫
      (cyclicHomAuxiliary n).left)).appTop.hom
  rw [Category.assoc, Category.assoc, hs, ← Category.assoc]
  exact normalizedSliceFamily_satisfies _

/-- Normalization restricts to the identity on the actual normalized subgroup locus. -/
@[reassoc] theorem cyclicHomNormalizedLocusInclusion_normalization :
    cyclicHomNormalizedLocusInclusion n ≫ cyclicHomLocusNormalization n = 𝟙 _ := by
  rw [cyclicHomLocusNormalization_comp]
  apply (cancel_mono (cyclicHomNormalizedLocusInclusion n)).mp
  apply (cancel_mono (cyclicHomUniversalMultiplicationLocusInclusion n)).mp
  simp only [Category.assoc, cyclicHomNormalizedLocusPoint_parameter, Category.id_comp]
  apply cyclicHomNormalizedPoint_fixed
  simpa only [Category.id_comp] using cyclicHomNormalizedLocus_satisfies n
    (𝟙 (cyclicHomNormalizedLocus n))

end FLT.Mazur.OddWeierstrassParameter
