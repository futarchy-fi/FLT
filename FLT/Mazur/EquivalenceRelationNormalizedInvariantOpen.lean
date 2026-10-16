/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryActionGeometry

/-!
# Original invariant source domains for moving normalized frames

Pulling an invariant original source open back by the moving first endpoint
gives a stable normalized open. Its exact boundary lies over the corresponding
original closed source domain, so coefficients on that domain can be pulled back.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (W : A.Opens) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)

include hW in
/-- Original invariance makes the first-endpoint inverse image stable under moving permutations. -/
theorem first_preimage_stable (σ : Equiv.Perm I) :
    (action e I o σ).hom ⁻¹ᵁ (first p q I o ⁻¹ᵁ W) = first p q I o ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, ← actionArrow_second,
    Scheme.Hom.comp_preimage, ← hW, ← Scheme.Hom.comp_preimage, actionArrow_first]

namespace InvariantBoundary
variable {B C : Scheme} (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)

omit [IsSeparated p] [Mono i] in
include hW hr hs in
/-- The exact original boundary domain is invariant under the entire original closed relation. -/
theorem original_open_invariant : r ⁻¹ᵁ (i ⁻¹ᵁ W) = s ⁻¹ᵁ (i ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, ← hr.w, Scheme.Hom.comp_preimage,
    hW, ← Scheme.Hom.comp_preimage, hs, Scheme.Hom.comp_preimage]

omit [Mono i] in
/-- The boundary-domain pullback is exact, including its scheme open and all coefficients. -/
theorem endpoint_preimage_eq :
    endpoint (p := p) (q := q) I o i ⁻¹ᵁ (i ⁻¹ᵁ W) =
      inclusion I o i ⁻¹ᵁ (first p q I o ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, ← endpoint_condition, Scheme.Hom.comp_preimage]

omit [Mono i] in
/-- A source chart inside the original domain has its whole boundary inside that domain. -/
theorem boundary_chart_le (U : (source p q I o).Opens)
    (hU : U ≤ first p q I o ⁻¹ᵁ W) :
    inclusion I o i ⁻¹ᵁ U ≤ endpoint I o i ⁻¹ᵁ (i ⁻¹ᵁ W) := by
  rw [endpoint_preimage_eq]
  exact (TopologicalSpace.Opens.map (inclusion I o i).base).monotone hU

end InvariantBoundary
end FLT.Mazur.EquivalenceRelationNormalizedFrames
