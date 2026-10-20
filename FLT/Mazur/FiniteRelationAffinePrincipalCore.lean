/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTargetNormCore
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Affine invariant cores without an affine ambient source

An affine principal open containing a whole orbit has an affine norm core.
The full original equivalence operations prove its invariance. This applies
to locally closed rank stages whose entire source need not be affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationAffinePrincipalCore
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme} {p q : D ⟶ A} (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Whole-orbit containment is unchanged along an arbitrary original arrow. -/
theorem wholeFiber_endpoints (W : Set A) (z : D) :
    (∀ w : D, p w = p z → q w ∈ W) ↔ (∀ w : D, p w = q z → q w ∈ W) := by
  have step (a : D) (ha : ∀ w : D, p w = p a → q w ∈ W) :
      ∀ w : D, p w = q a → q w ∈ W := by
    intro w hw
    obtain ⟨v, hv, hv'⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_isLimit e.isLimit) a w hw.symm
    have hp : p (e.t v) = p a :=
      (congrArg (fun g ↦ g v) e.transitivity₁).trans (congrArg p hv)
    have hq : q (e.t v) = q w :=
      (congrArg (fun g ↦ g v) e.transitivity₂).trans (congrArg q hv')
    exact hq ▸ ha _ hp
  refine ⟨step z, fun h ↦ ?_⟩
  have hp : p (e.s z) = q z := congrArg (fun g ↦ g z) e.symmetry₁
  have hq : q (e.s z) = p z := congrArg (fun g ↦ g z) e.symmetry₂
  simpa only [hq] using step (e.s z) (by simpa only [hp] using h)

variable [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (a : Γ(A, ⊤)) (ha : IsAffineOpen (A.basicOpen a))

/-- A norm over the affine principal domain retains every arrow leaving that domain. -/
def core : A.Opens := FiniteTargetNormCore.core p q ⟨A.basicOpen a, ha⟩
  (by rw [SchemeOpenEnvelope.finiteTargetOpen_eq_top p]; exact le_top) a

include e in
/-- Reflexivity removes the apparent extra condition of membership in the input open. -/
theorem mem_core_iff (x : A) : x ∈ core (p := p) (q := q) a ha ↔
    ∀ z : D, p z = x → q z ∈ A.basicOpen a := by
  rw [core, FiniteTargetNormCore.mem_core_iff]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  have hp : p (e.r x) = x := congrArg (fun g ↦ g x) e.reflexivity₁
  have hq : q (e.r x) = x := congrArg (fun g ↦ g x) e.reflexivity₂
  exact hq ▸ h _ hp

/-- The invariant core is affine even if the original ambient source is not. -/
theorem core_isAffine : IsAffineOpen (core (p := p) (q := q) a ha) :=
  FiniteTargetNormCore.core_isAffine _ _ _ _ _

/-- The core refines the supplied affine principal neighborhood. -/
theorem core_le : core (p := p) (q := q) a ha ≤ A.basicOpen a :=
  FiniteTargetNormCore.core_le _ _ _ _ _

include e in
/-- The whole relation preserves the constructed affine core exactly. -/
theorem core_invariant :
    p ⁻¹ᵁ core (p := p) (q := q) a ha = q ⁻¹ᵁ core (p := p) (q := q) a ha := by
  ext z
  change p z ∈ core (p := p) (q := q) a ha ↔ q z ∈ core (p := p) (q := q) a ha
  rw [mem_core_iff e, mem_core_iff e]
  exact wholeFiber_endpoints e _ z

end FLT.Mazur.FiniteRelationAffinePrincipalCore
