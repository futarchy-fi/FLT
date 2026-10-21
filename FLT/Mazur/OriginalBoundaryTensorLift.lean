/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatInvariantBoundaryMultiplier
public import FLT.Mazur.RankStageOriginalBoundaryLiftIdeal

/-!
# Actual original boundary corrections from flat tensor numerators

The numerator need only exist over a flat algebra of the original invariant
ring. Full endpoint equations and the literal full boundary equation construct
an original multiplier and lift. A chosen raw original lift then yields an
actual boundary-zero correction with the unchanged full discrepancy.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections RingPairInvariantFlatScalars FlatAlgebraEqualizer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} (J : A.IdealSheafData)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra

/-- The original full boundary as an algebra over the actual invariant ring. -/
@[instance_reducible]
def originalBoundaryAlgebra : Algebra R Γ(J.subscheme, ⊤) :=
  (J.subschemeι.appTop.hom.comp (Subring.subtype R)).toAlgebra

attribute [local instance] originalBoundaryAlgebra

/-- Full original boundary restriction over the original invariant scalars. -/
def originalBoundaryMap : Γ(A, ⊤) →ₐ[R] Γ(J.subscheme, ⊤) :=
  ⟨J.subschemeι.appTop.hom, fun _ ↦ rfl⟩

variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
  [Module.Flat (invariants p.appTop.hom q.appTop.hom) S]
local notation "α" => first p.appTop.hom q.appTop.hom
local notation "β" => second p.appTop.hom q.appTop.hom

/-- A branch-only numerator constructs a nonvanishing member of the exact original lift ideal. -/
theorem exists_originalBoundaryLift_multiplier_of_tensor
    (P : Ideal S) (t : Γ(J.subscheme, ⊤)) (s : S) (hs : s ∉ P)
    (a : S ⊗[R] Γ(A, ⊤)) (he : tensorMap S α a = tensorMap S β a)
    (hb : tensorMap S (originalBoundaryMap J) a =
      algebraMap S (S ⊗[R] Γ(J.subscheme, ⊤)) s * (1 ⊗ₜ[R] t)) :
    ∃ r : R, algebraMap R S r ∉ P ∧ r ∈ originalBoundaryLiftIdeal J t :=
  FlatInvariantBoundaryMultiplier.exists_original_multiplier
    p.appTop.hom q.appTop.hom (originalBoundaryMap J) S P t s hs a he hb

/-- Descent produces an actual boundary-zero change of any chosen original raw lift. -/
theorem exists_originalBoundary_correction_of_tensor
    (P : Ideal S) (t : Γ(J.subscheme, ⊤)) (s : S) (hs : s ∉ P)
    (a : S ⊗[R] Γ(A, ⊤)) (he : tensorMap S α a = tensorMap S β a)
    (hb : tensorMap S (originalBoundaryMap J) a =
      algebraMap S (S ⊗[R] Γ(J.subscheme, ⊤)) s * (1 ⊗ₜ[R] t))
    (b : Γ(A, ⊤)) (hb₀ : J.subschemeι.appTop b = t) :
    ∃ (r : R) (z : Γ(A, ⊤)), algebraMap R S r ∉ P ∧
      J.subschemeι.appTop z = 0 ∧
      p.appTop z - q.appTop z = p.appTop r.val * (p.appTop b - q.appTop b) := by
  obtain ⟨r, hr, w, hw⟩ :=
    exists_originalBoundaryLift_multiplier_of_tensor J S P t s hs a he hb
  refine ⟨r, r.val * b - w.val, hr, ?_, ?_⟩
  · rw [map_sub, map_mul, hb₀, hw, sub_self]
  · have hrq : p.appTop r.val = q.appTop r.val := r.property
    have hwq : p.appTop w.val = q.appTop w.val := w.property
    simp only [map_sub, map_mul, ← hrq, ← hwq]
    ring

end FLT.Mazur.EquivalenceRelationOrderedFrames
