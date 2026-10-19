/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Prod

/-!
# The exact torsion group in the narrow Mazur input

For odd p the full two-torsion together with p-torsion is Z/2 × Z/(2p).
The Chinese remainder equivalence retains the independent two-torsion factor.
-/

@[expose] public section

namespace FLT.Mazur

/-- The full Frey torsion configuration in invariant-factor form. -/
def fullTwoPrimeTorsionEquiv (p : ℕ) (hp : Nat.Coprime 2 p) :
    ((ZMod 2 × ZMod 2) × ZMod p) ≃+ (ZMod 2 × ZMod (2 * p)) :=
  AddEquiv.prodAssoc.trans
    ((AddEquiv.refl _).prodCongr (ZMod.chineseRemainder hp).symm.toAddEquiv)

/-- Excluding either presentation excludes precisely the same subgroup embeddings. -/
theorem fullTwoPrime_embedding_iff {A : Type*} [AddCommGroup A]
    (p : ℕ) (hp : Nat.Coprime 2 p) :
    (∃ f : ((ZMod 2 × ZMod 2) × ZMod p) →+ A, Function.Injective f) ↔
      ∃ f : (ZMod 2 × ZMod (2 * p)) →+ A, Function.Injective f := by
  let e := fullTwoPrimeTorsionEquiv p hp
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.comp e.symm.toAddMonoidHom, hf.comp e.symm.injective⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.comp e.toAddMonoidHom, hf.comp e.injective⟩

end FLT.Mazur
