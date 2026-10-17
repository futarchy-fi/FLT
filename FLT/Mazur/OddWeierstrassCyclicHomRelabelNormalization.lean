/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomAffinePresentationInvariant
public import FLT.Mazur.OddWeierstrassCyclicHomRelabeledNormalizationIso

/-!
# Full normalization absorbs intermediate normalization before relabeling

The actual marked comparison proves absorption on affine tests, and full
normalization naturality descends it to arbitrary source schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n)))
  {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "r" => Over.Hom.left (cyclicHomRelabel n a c)

/-- Intermediate normalization before relabeling does not change the actual affine parameter. -/
theorem cyclicHomNormalizedPoint_relabel_normalize_affine [IsAffine T] :
    cyclicHomNormalizedPoint n (cyclicHomNormalizedPoint n f ≫ r) =
      cyclicHomNormalizedPoint n (f ≫ r) :=
  cyclicHomNormalizedPoint_invariant_of_affine_iso n _ _
    (cyclicHomRelabeledNormalizationIso n a c f)
    (cyclicHomRelabeledNormalizationIso_auxiliary n a c f)
    (cyclicHomRelabeledNormalizationIso_cyclic n a c f)

/-- Absorption holds on every original source scheme, with all cyclic values retained. -/
theorem cyclicHomNormalizedPoint_relabel_normalize :
    cyclicHomNormalizedPoint n (cyclicHomNormalizedPoint n f ≫ r) =
      cyclicHomNormalizedPoint n (f ≫ r) := by
  apply cyclicHomNormalizedPoint_invariant_of_affine_tests
  intro R _ k
  have h := cyclicHomProperRelated_of_affine_iso n _ _
    (cyclicHomRelabeledNormalizationIso n a c (k ≫ f))
    (cyclicHomRelabeledNormalizationIso_auxiliary n a c (k ≫ f))
    (cyclicHomRelabeledNormalizationIso_cyclic n a c (k ≫ f))
  simpa only [cyclicHomNormalizedPoint_natural, Category.assoc] using h

end FLT.Mazur.OddWeierstrassParameter
