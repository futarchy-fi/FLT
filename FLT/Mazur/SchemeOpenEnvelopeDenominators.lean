/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Coefficient denominators supported in an open envelope

Coefficients whose principal opens lie in a prescribed open form a radical
ideal. For an open immersion, each such coefficient constructs an actual
lift from the whole principal envelope, with a Cartesian square. Existence
of coefficients avoiding a given point is not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u v
variable {C : Type u} [CommRing C] {Y : Scheme.{v}}
  (φ : C →+* Γ(Y, ⊤)) (U : Y.Opens)

/-- All coefficients whose full principal domains are contained in the prescribed open. -/
def denominatorIdeal : Ideal C where
  carrier := {r | Y.basicOpen (φ r) ≤ U}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change Y.basicOpen (φ (a + b)) ≤ U
    simpa only [map_add] using (Y.basicOpen_add_le (φ a) (φ b)).trans (sup_le ha hb)
  smul_mem' := by
    intro a b hb
    change Y.basicOpen (φ (a * b)) ≤ U
    rw [map_mul, Scheme.basicOpen_mul]
    exact inf_le_right.trans hb

/-- Membership records full principal-domain containment, not just a pointwise chosen lift. -/
theorem mem_denominatorIdeal (r : C) :
    r ∈ denominatorIdeal φ U ↔ Y.basicOpen (φ r) ≤ U := Iff.rfl

/-- Taking a positive power changes no admissible principal neighborhood. -/
theorem pow_mem_denominatorIdeal_iff (r : C) {n : ℕ} (hn : 0 < n) :
    r ^ n ∈ denominatorIdeal φ U ↔ r ∈ denominatorIdeal φ U := by
  change Y.basicOpen (φ (r ^ n)) ≤ U ↔ Y.basicOpen (φ r) ≤ U
  rw [map_pow, Scheme.basicOpen_pow Y (φ r) hn]

/-- These actual denominators form a radical ideal. -/
theorem denominatorIdeal_isRadical : (denominatorIdeal φ U).IsRadical := by
  rw [Ideal.isRadical_iff_pow_one_lt 2 (by decide)]
  intro r hr
  exact (pow_mem_denominatorIdeal_iff φ U r (by decide : 0 < 2)).mp hr

/-- The ideal is the unit ideal precisely when the entire envelope is in the prescribed open. -/
theorem denominatorIdeal_eq_top_iff : denominatorIdeal φ U = ⊤ ↔ U = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  change Y.basicOpen (φ 1) ≤ U ↔ U = ⊤
  rw [map_one, Scheme.basicOpen_one, top_le_iff]

variable {Z : Scheme.{v}} (j : Z ⟶ Y) [IsOpenImmersion j]

/-- A genuine denominator constructs a lift on the entire principal envelope. -/
def principalLift (r : C) (hr : r ∈ denominatorIdeal φ j.opensRange) :
    (Y.basicOpen (φ r)).toScheme ⟶ Z :=
  IsOpenImmersion.lift j (Y.basicOpen (φ r)).ι (by
    rintro _ ⟨x, rfl⟩
    exact hr x.property)

/-- The constructed lift keeps the original envelope inclusion exactly. -/
@[reassoc]
theorem principalLift_ι (r : C) (hr : r ∈ denominatorIdeal φ j.opensRange) :
    principalLift φ j r hr ≫ j = (Y.basicOpen (φ r)).ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The principal envelope is the actual full pullback of the original open relation. -/
theorem principalLift_isPullback (r : C)
    (hr : r ∈ denominatorIdeal φ j.opensRange) :
    IsPullback (principalLift φ j r hr) (𝟙 _) j (Y.basicOpen (φ r)).ι :=
  IsOpenImmersion.isPullback_lift_id _ _ _

/-- Unit ideal is equivalent to invertibility of the original envelope inclusion. -/
theorem denominatorIdeal_eq_top_iff_isIso :
    denominatorIdeal φ j.opensRange = ⊤ ↔ IsIso j := by
  rw [denominatorIdeal_eq_top_iff]
  constructor
  · exact isIso_of_isOpenImmersion_of_opensRange_eq_top j
  · intro hj
    ext y
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨inv j y, ?_⟩
      change (inv j ≫ j) y = y
      rw [IsIso.inv_hom_id]
      rfl

end FLT.Mazur.SchemeOpenEnvelope
