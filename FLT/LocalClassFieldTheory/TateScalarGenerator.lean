/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateScalarAbelianization
public import FLT.LocalClassFieldTheory.TateCocycleClass

/-!
# Scalar generators in Tate degree minus two

The single bar chain at a group element is a scalar cycle. Its class gives
an explicit input on which the two connecting maps can be evaluated.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupHomology

variable (k G : Type) [CommRing k] [Group G] [Fintype G]

local notation "T" => Rep.trivial k G k

/-- The scalar single bar chain is a cycle in the actual Tate complex. -/
theorem tateScalarGenerator_cycle (g : G) :
    (tateComplex T).d (-2) (-2 + 1)
      ((chainsIso₁ T).inv (Finsupp.single g (1 : k))) = 0 := by
  have h := congrArg (fun f => f.hom (Finsupp.single g (1 : k))) (eq_d₁₀_comp_inv T)
  change (tateComplex T).d (-2) (-1)
    ((chainsIso₁ T).inv (Finsupp.single g (1 : k))) =
      (chainsIso₀ T).inv (d₁₀ T (Finsupp.single g (1 : k))) at h
  have hz : d₁₀ T (Finsupp.single g (1 : k)) = 0 := by
    rw [d₁₀_single]
    exact sub_self _
  rw [hz, map_zero] at h
  exact h

/-- The scalar Tate class represented by a single bar generator. -/
def tateScalarGenerator (g : G) : tateCohomology T (-2) :=
  tateCocycleClass T (-2) ((chainsIso₁ T).inv (Finsupp.single g (1 : k)))
    (tateScalarGenerator_cycle k G g)

end LocalClassFieldTheory
