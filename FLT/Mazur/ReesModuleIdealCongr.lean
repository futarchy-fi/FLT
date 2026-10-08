/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Coefficient-preserving comparison for equal Rees ideals

Keep the equality transport abstract in the coefficient ring and module.
This avoids unfolding geometric scalar structures when comparing actual
chart ideals with extensions of base ideals.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.Rees

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
  (I J : Ideal S) (h : I = J)

/-- Equal ideals give linear coordinates on their ordinary power Rees modules. -/
def powerModuleCongr : (I.stableFiltration (⊤ : Submodule S M)).submodule ≃ₗ[S]
    (J.stableFiltration (⊤ : Submodule S M)).submodule :=
  LinearEquiv.ofEq
    ((I.stableFiltration (⊤ : Submodule S M)).submodule.restrictScalars S)
    ((J.stableFiltration (⊤ : Submodule S M)).submodule.restrictScalars S)
    (by rw [h])

/-- The comparison is the identity on the ambient polynomial module. -/
lemma powerModuleCongr_val (s : (I.stableFiltration (⊤ : Submodule S M)).submodule) :
    (powerModuleCongr I J h s).val = s.val := rfl

attribute [irreducible] powerModuleCongr

end FLT.Mazur.Rees
