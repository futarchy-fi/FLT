/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomLocusNormalizationRelation
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedRelabelAction

/-!
# Independent relabeling preserves the actual subgroup presentation relation

Normalization equivariance gives a genuine endomorphism of the kernel pair.
Its two original subgroup projections satisfy the product composition law.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Equal full normalized subgroup parameters remain equal after independent relabeling. -/
theorem cyclicHomLocusRelation_relabel_eq {T : Scheme}
    (f g : T ⟶ cyclicHomUniversalMultiplicationLocus n)
    (h : f ≫ cyclicHomLocusNormalization n = g ≫ cyclicHomLocusNormalization n)
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    (f ≫ cyclicHomLocusRelabel n a c) ≫ cyclicHomLocusNormalization n =
      (g ≫ cyclicHomLocusRelabel n a c) ≫ cyclicHomLocusNormalization n := by
  simpa only [Category.assoc, cyclicHomLocusNormalization_equivariant] using
    congrArg (fun z ↦ z ≫ cyclicHomNormalizedRelabel n a c) h

/-- Relabel both original subgroups in the represented presentation relation. -/
def cyclicHomLocusRelationRelabel
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomLocusNormalizationRelation n ⟶ cyclicHomLocusNormalizationRelation n :=
  cyclicHomLocusRelationPoint n
    (cyclicHomLocusRelationFirst n ≫ cyclicHomLocusRelabel n a c)
    (cyclicHomLocusRelationSecond n ≫ cyclicHomLocusRelabel n a c)
    (cyclicHomLocusRelation_relabel_eq n _ _ (cyclicHomLocusRelation_condition n) a c)

/-- The first original subgroup follows the prescribed full relabeling. -/
@[reassoc] theorem cyclicHomLocusRelationRelabel_first
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomLocusRelationRelabel n a c ≫ cyclicHomLocusRelationFirst n =
      cyclicHomLocusRelationFirst n ≫ cyclicHomLocusRelabel n a c :=
  cyclicHomLocusRelationPoint_first n _ _ _

/-- The second original subgroup follows the same prescribed full relabeling. -/
@[reassoc] theorem cyclicHomLocusRelationRelabel_second
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomLocusRelationRelabel n a c ≫ cyclicHomLocusRelationSecond n =
      cyclicHomLocusRelationSecond n ≫ cyclicHomLocusRelabel n a c :=
  cyclicHomLocusRelationPoint_second n _ _ _

/-- Identity relabeling fixes the complete original presentation relation. -/
theorem cyclicHomLocusRelationRelabel_one : cyclicHomLocusRelationRelabel n 1 1 = 𝟙 _ := by
  apply cyclicHomLocusRelation_hom_ext
  · rw [cyclicHomLocusRelationRelabel_first, cyclicHomLocusRelabel_one,
      Category.comp_id, Category.id_comp]
  · rw [cyclicHomLocusRelationRelabel_second, cyclicHomLocusRelabel_one,
      Category.comp_id, Category.id_comp]

/-- Composition on the actual relation agrees with the full product relabeling law. -/
theorem cyclicHomLocusRelationRelabel_mul
    (a b : MulAut (Labels 3)) (c d : MulAut (Multiplicative (ZMod n))) :
    cyclicHomLocusRelationRelabel n (a * b) (c * d) =
      cyclicHomLocusRelationRelabel n b d ≫ cyclicHomLocusRelationRelabel n a c := by
  apply cyclicHomLocusRelation_hom_ext
  · rw [cyclicHomLocusRelationRelabel_first, Category.assoc,
      cyclicHomLocusRelationRelabel_first, cyclicHomLocusRelationRelabel_first_assoc,
      cyclicHomLocusRelabel_mul]
  · rw [cyclicHomLocusRelationRelabel_second, Category.assoc,
      cyclicHomLocusRelationRelabel_second, cyclicHomLocusRelationRelabel_second_assoc,
      cyclicHomLocusRelabel_mul]

end FLT.Mazur.OddWeierstrassParameter
