/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLabelHom
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclicity and divisibility for the split component quotient

The additive label embeds the actual quotient E/E₀ into Z/nZ. Therefore the
quotient is cyclic and its order divides n. Exact order n still requires
lifting enough labels; neither completeness nor label surjectivity is assumed.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)

include D

/-- The actual component quotient of a deep split model is cyclic. -/
theorem isAddCyclic_ellipticComponentQuotient_of_splitNodeDepth :
    IsAddCyclic (EllipticComponentQuotient A W) :=
  isAddCyclic_of_injective (nodeComponentLabelHom D) (nodeComponentLabelHom_injective D)

/-- The number of actual rational component classes divides the split depth. -/
theorem natCard_ellipticComponentQuotient_dvd_splitNodeDepth :
    Nat.card (EllipticComponentQuotient A W) ∣ n := by
  simpa only [Nat.card_zmod] using AddSubgroup.card_dvd_of_injective
    (nodeComponentLabelHom D) (nodeComponentLabelHom_injective D)

/-- A generic point represents a generator of the actual finite component quotient. -/
theorem exists_point_generating_splitNodeComponents :
    ∃ P : (W.map (algebraMap A K)).toProjective.Point,
      ∀ c : EllipticComponentQuotient A W, ∃ m : ℤ, m • ellipticComponentHom A W P = c := by
  let := isAddCyclic_ellipticComponentQuotient_of_splitNodeDepth D
  obtain ⟨c, hc⟩ := exists_zsmul_surjective (EllipticComponentQuotient A W)
  obtain ⟨P, hP⟩ := ellipticComponentHom_surjective A W c
  exact ⟨P, hP ▸ hc⟩

end FLT.Mazur
