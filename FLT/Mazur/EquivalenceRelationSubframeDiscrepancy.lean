/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundarySubframeRefinement

/-!
# Exact discrepancies between independent lifts on nested subframe charts

The discrepancy is a function on the actual larger source chart. It vanishes
on its whole original boundary and obeys a cocycle law under nested selections.
Subtracting it corrects one selection; simultaneous invariant correction is separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
  (o : I) (o' : J) (ι : J ↪ I)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (hUV : U ≤ subframeMap e o o' ι ⁻¹ᵁ V)

/-- The actual difference of independent lifts, on the larger source chart. -/
def subframeDiscrepancy (u : Γ(U.toScheme, ⊤)) (v : Γ(V.toScheme, ⊤)) :
    Γ(U.toScheme, ⊤) := u - (subframeRefinementMap e o o' ι U V hUV).appTop v

/-- Vanishing is precisely compatibility along this subframe selection. -/
theorem subframeDiscrepancy_eq_zero_iff (u : Γ(U.toScheme, ⊤)) (v : Γ(V.toScheme, ⊤)) :
    subframeDiscrepancy e o o' ι U V hUV u v = 0 ↔
      u = (subframeRefinementMap e o o' ι U V hUV).appTop v := sub_eq_zero

/-- The discrepancy is an explicit correction solving the selected source equation. -/
theorem subframeDiscrepancy_correct (u : Γ(U.toScheme, ⊤)) (v : Γ(V.toScheme, ⊤)) :
    u - subframeDiscrepancy e o o' ι U V hUV u v =
      (subframeRefinementMap e o o' ι U V hUV).appTop v := sub_sub_cancel _ _

/-- Corrections for successive strict subframes satisfy the exact additive cocycle law. -/
theorem subframeDiscrepancy_cocycle (o'' : H) (κ : H ↪ J)
    (Z : (source p q H o'').Opens) (hVZ : V ≤ subframeMap e o' o'' κ ⁻¹ᵁ Z)
    (hUZ : U ≤ subframeMap e o o'' (κ.trans ι) ⁻¹ᵁ Z)
    (u : Γ(U.toScheme, ⊤)) (v : Γ(V.toScheme, ⊤)) (w : Γ(Z.toScheme, ⊤)) :
    subframeDiscrepancy e o o'' (κ.trans ι) U Z hUZ u w =
      subframeDiscrepancy e o o' ι U V hUV u v +
        (subframeRefinementMap e o o' ι U V hUV).appTop
          (subframeDiscrepancy e o' o'' κ V Z hVZ v w) := by
  simp only [subframeDiscrepancy, map_sub,
    subframeRefinement_appTop_comp e o o' ι U V hUV o'' κ Z hVZ hUZ]
  abel

/-- Changing independent lifts changes the discrepancy by the corresponding coboundary. -/
theorem subframeDiscrepancy_sub (u du : Γ(U.toScheme, ⊤)) (v dv : Γ(V.toScheme, ⊤)) :
    subframeDiscrepancy e o o' ι U V hUV (u - du) (v - dv) =
      subframeDiscrepancy e o o' ι U V hUV u v -
        subframeDiscrepancy e o o' ι U V hUV du dv := by
  simp only [subframeDiscrepancy, map_sub]
  abel

namespace InvariantBoundary
variable {B C : Scheme.{0}} (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "jU" => inclusion (p := p) (q := q) I o i
local notation "jV" => inclusion (p := p) (q := q) J o' i
variable (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
  (hU : (inclusion (p := p) (q := q) I o i ⁻¹ᵁ U) ≤
    endpoint (p := p) (q := q) I o i ⁻¹ᵁ E)
  (hV : (inclusion (p := p) (q := q) J o' i ⁻¹ᵁ V) ≤
    endpoint (p := p) (q := q) J o' i ⁻¹ᵁ E)

include hr hs in
/-- Independent exact lifts differ by an actual boundary-zero function, including nilpotents. -/
theorem subframeDiscrepancy_boundary_zero (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (u : Γ(U.toScheme, ⊤)) (v : Γ(V.toScheme, ⊤))
    (hu : ((jU) ∣_ U).appTop u = ((endpoint I o i).resLE E (jU ⁻¹ᵁ U) hU).appTop t)
    (hv : ((jV) ∣_ V).appTop v = ((endpoint J o' i).resLE E (jV ⁻¹ᵁ V) hV).appTop t) :
    ((jU) ∣_ U).appTop (subframeDiscrepancy e o o' ι U V hUV u v) = 0 := by
  rw [subframeDiscrepancy, map_sub,
    subframeBoundaryRefinement_lift e o o' ι i z r s hr hs U V hUV E hE hU hV t ht v hv,
    hu, sub_self]

end InvariantBoundary
end FLT.Mazur.EquivalenceRelationNormalizedFrames
