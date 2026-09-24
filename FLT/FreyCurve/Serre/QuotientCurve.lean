/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.FixedLineDescent

/-!
# Point-level consequences of a quotient isogeny

These lemmas isolate the algebra and descent needed for the trivial-quotient branch of
Serre's argument. Constructing the quotient elliptic curve and its geometric point map
remains a separate geometric input.
-/

@[expose] public section

namespace AddMonoidHom

/-- A map with the same kernel as a surjection induces an injection from its target. -/
theorem exists_injective_factor_of_ker_eq {A B C : Type*}
    [AddGroup A] [AddGroup B] [AddGroup C]
    (q : A →+ B) (hq : Function.Surjective q) (f : A →+ C)
    (hker : q.ker = f.ker) :
    ∃ j : B →+ C, Function.Injective j ∧ ∀ a, j (q a) = f a := by
  let j := q.liftOfSurjective hq ⟨f, hker.le⟩
  have hj (a : A) : j (q a) = f a :=
    q.liftOfRightInverse_comp_apply _ _ _ a
  refine ⟨j, (injective_iff_map_eq_zero j).mpr ?_, hj⟩
  intro b hb
  obtain ⟨a, rfl⟩ := hq b
  have ha : a ∈ f.ker := (hj a).symm.trans hb
  exact show a ∈ q.ker from hker.symm ▸ ha

end AddMonoidHom
