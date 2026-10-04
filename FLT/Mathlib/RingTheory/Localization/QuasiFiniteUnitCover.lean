/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.RingHom.QuasiFinite

/-! # Assemble quasi-finiteness from a unit-ideal principal cover -/

@[expose] public noncomputable section

namespace Algebra

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Quasi-finiteness on principal opens generating the unit ideal implies global
quasi-finiteness. This statement keeps the indexed cover used in coefficient descent. -/
theorem quasiFinite_of_unit_principal_cover {ι : Type*} (a : ι → A)
    (hspan : Ideal.span (Set.range a) = ⊤)
    (h : ∀ i, QuasiFinite R (Localization.Away (a i))) : QuasiFinite R A := by
  apply RingHom.quasiFinite_algebraMap.mp
  apply RingHom.QuasiFinite.ofLocalizationSpanTarget (algebraMap R A) (Set.range a) hspan
  rintro ⟨x, i, rfl⟩
  have := h i
  rw [← IsScalarTower.algebraMap_eq R A (Localization.Away (a i))]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

end Algebra
