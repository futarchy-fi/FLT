/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationPrincipalBoundaryCover
public import FLT.Mazur.InvariantOpenGlobalRestriction

/-!
# Homogeneous corrections on a finite invariant principal cover

Starting with independent local lifts, construct actual boundary-zero
corrections on each whole principal patch. Subtracting them kills every
pairwise overlap error. The construction is on an affine source at a fixed
order; it does not assert compatible choices across an infinite tower.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationPrincipalBoundaryCover
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
open SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency true
set_option quotPrecheck false
private theorem global_overlap {X : Scheme.{0}} (U V : X.Opens) (w : Γ(X, ⊤)) :
    (X.homOfLE (inf_le_left : U ⊓ V ≤ U)).appTop (U.ι.appTop w) =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).appTop (V.ι.appTop w) := by
  change (X.homOfLE inf_le_left ≫ U.ι).appTop w =
    (X.homOfLE inf_le_right ≫ V.ι).appTop w
  rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]

variable {D X Y : Scheme.{0}} (p q : D ⟶ X) [IsAffine X] [IsAffine D]
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type*} [Finite ι] (r : ι → compatibleFunctions p q)
  (i : Y ⟶ X) [IsAffine Y]
local notation "U" j => X.basicOpen (r j).val
local notation "hU" j => compatibleFunctions_basicOpen p q (r j)

attribute [local irreducible] globalRestriction

include e in
/-- Exact full-boundary corrections on every patch kill all actual overlap errors. -/
theorem exists_homogeneous_corrections (hr : (⨆ j, U j) = ⊤)
    (v : ∀ j, coefficients p q (U j) (hU j)) (t : Γ(Y, ⊤))
    (hv : ∀ j, (principalPullbackMap i (r j).val).appTop (v j).val =
      (Y.basicOpen (i.appTop (r j).val)).ι.appTop t) :
    ∃ c : ∀ j, coefficients p q (U j) (hU j),
      (∀ j, (principalPullbackMap i (r j).val).appTop (c j).val = 0) ∧
      ∀ j l,
        (X.homOfLE (inf_le_left : (U j) ⊓ (U l) ≤ (U j))).appTop (v j - c j).val =
          (X.homOfLE (inf_le_right : (U j) ⊓ (U l) ≤ (U l))).appTop (v l - c l).val := by
  obtain ⟨w, hw⟩ := exists_boundary_lift p q e r i hr v t hv
  let c (j : ι) := v j - globalRestriction p q (U j) (hU j) w
  have hc (j : ι) : v j - c j = globalRestriction p q (U j) (hU j) w :=
    sub_sub_cancel _ _
  have hfix (j : ι) : (v j - c j).val = (U j).ι.appTop w.val :=
    (congrArg Subtype.val (hc j)).trans (globalRestriction_val p q (U j) (hU j) w)
  refine ⟨c, ?_, ?_⟩
  · intro j
    change (principalPullbackMap i (r j).val).appTop
      ((v j).val - (globalRestriction p q (U j) (hU j) w).val) = 0
    have hg := (congrArg (principalPullbackMap i (r j).val).appTop
      (globalRestriction_val p q (U j) (hU j) w)).trans
      ((principalPullbackMap_appTop i (r j).val w.val).trans
        (congrArg (Y.basicOpen (i.appTop (r j).val)).ι.appTop hw))
    exact (map_sub (principalPullbackMap i (r j).val).appTop.hom _ _).trans
      ((congrArg₂ (fun x y ↦ x - y) (hv j) hg).trans (sub_self _))
  · intro j l
    have hj := congrArg
      (X.homOfLE (inf_le_left : (U j) ⊓ (U l) ≤ (U j))).appTop (hfix j)
    have hl := congrArg
      (X.homOfLE (inf_le_right : (U j) ⊓ (U l) ≤ (U l))).appTop (hfix l)
    refine hj.trans (Eq.trans ?_ hl.symm)
    exact global_overlap (U j) (U l) w.val

end FLT.Mazur.FiniteRelationPrincipalBoundaryCover
