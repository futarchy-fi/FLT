/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualProjection

/-!
# The exact residual point relation on the assembled finite quotient

The relation is witnessed by one point of the original full comparison scheme.
Its quotient is canonically the full orbit space: no extra equivalence closure
or deletion of residual comparisons is involved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "Q" => normalizedDisjointQuotient n
local notation "q" => normalizedDisjointQuotientMap n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- One original comparison point witnesses the residual relation on finite quotient points. -/
def ResidualRelated (x y : Q) : Prop :=
  ∃ a : disjointComparisonArrows n, q (src a) = x ∧ q (tgt a) = y

/-- Equality in the full orbit space is exactly the original residual comparison relation. -/
theorem residualProjection_eq_iff (x y : Q) :
    residualProjection n x = residualProjection n y ↔ ResidualRelated n x y := by
  obtain ⟨u, rfl⟩ := (q).surjective x
  obtain ⟨v, rfl⟩ := (q).surjective y
  rw [residualProjection_apply, residualProjection_apply]
  constructor
  · intro h
    obtain ⟨a, ha, hb⟩ := (projection_eq_iff n u v).mp h
    exact ⟨a, congrArg q ha, congrArg q hb⟩
  · rintro ⟨a, ha, hb⟩
    exact (projection_eq_of_disjoint_quotient_eq n _ _ ha).symm.trans
      ((projection_pair n a).trans (projection_eq_of_disjoint_quotient_eq n _ _ hb))

/-- The actual residual point relation is already an equivalence relation. -/
def residualSetoid : Setoid Q where
  r := ResidualRelated n
  iseqv := ⟨fun x ↦ (residualProjection_eq_iff n x x).mp rfl,
    fun {x y} h ↦ (residualProjection_eq_iff n y x).mp
      ((residualProjection_eq_iff n x y).mpr h).symm,
    fun {x y z} h k ↦ (residualProjection_eq_iff n x z).mp
      (((residualProjection_eq_iff n x y).mpr h).trans
        ((residualProjection_eq_iff n y z).mpr k))⟩

/-- The quotient by the exact residual relation maps to the original full comparison orbits. -/
def residualOrbitMap : Quotient (residualSetoid n) → Orbit n :=
  Quotient.lift (residualProjection n) fun x y h ↦ (residualProjection_eq_iff n x y).mpr h

/-- On an original finite quotient point this is the residual projection. -/
theorem residualOrbitMap_mk (x : Q) :
    residualOrbitMap n (Quotient.mk (residualSetoid n) x) = residualProjection n x := rfl

/-- The residual quotient has exactly the same orbits as the full comparison scheme. -/
theorem residualOrbitMap_bijective : Function.Bijective (residualOrbitMap n) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro u v h
    exact Quotient.sound ((residualProjection_eq_iff n u v).mp h)
  · intro z
    obtain ⟨x, hx⟩ := (residualProjection_isQuotientMap n).surjective z
    exact ⟨Quotient.mk (residualSetoid n) x, hx⟩

/-- The actual residual quotient and full comparison orbit types are canonically equivalent. -/
def residualOrbitEquiv : Quotient (residualSetoid n) ≃ Orbit n :=
  Equiv.ofBijective (residualOrbitMap n) (residualOrbitMap_bijective n)

/-- The exact residual quotient carries the same quotient topology as the full orbit space. -/
def residualOrbitHomeomorph : Quotient (residualSetoid n) ≃ₜ Orbit n where
  toEquiv := residualOrbitEquiv n
  continuous_toFun :=
    isQuotientMap_quotient_mk'.continuous_iff.mpr (residualProjection_continuous n)
  continuous_invFun := by
    apply (residualProjection_isQuotientMap n).continuous_iff.mpr
    change Continuous ((residualOrbitEquiv n).symm ∘ residualProjection n)
    have he : (residualOrbitEquiv n).symm ∘ residualProjection n =
        Quotient.mk (residualSetoid n) := by
      funext x
      exact (residualOrbitEquiv n).symm_apply_apply (Quotient.mk (residualSetoid n) x)
    rw [he]
    exact continuous_quotient_mk'

/-- The residual homeomorphism retains the original finite quotient representatives. -/
theorem residualOrbitHomeomorph_mk (x : Q) :
    residualOrbitHomeomorph n (Quotient.mk (residualSetoid n) x) = residualProjection n x := rfl

end FLT.Mazur.CyclicCharacteristicOrbit
