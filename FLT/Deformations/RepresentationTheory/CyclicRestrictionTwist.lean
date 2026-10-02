/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.CyclicStableLinePair
public import FLT.Deformations.RepresentationTheory.PermutedSummandsTwist

/-!
# A quadratic self-twist from reducible cyclic restriction

An irreducible two-dimensional representation whose restriction to a normal
subgroup with cyclic quotient is reducible has a nontrivial quadratic
self-twist trivial on that subgroup. The stable-line pair, character and
intertwiner are all constructed from these hypotheses.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V) (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)]

/-- Reducible restriction across a cyclic quotient yields a nontrivial
quadratic self-twist in rank two and characteristic different from two. -/
theorem exists_quadratic_selfTwist (hV : Module.finrank k V = 2)
    (hchar : (2 : k) ≠ 0) (hirr : ρ.IsIrreducible)
    (hres : ¬ Representation.IsIrreducible (ρ.comp H.subtype)) :
    ∃ χ : G →* kˣ, χ ≠ 1 ∧ (∀ h : H, χ h = 1) ∧
      (∀ g, χ g ^ 2 = 1) ∧
      ∃ e : V ≃ₗ[k] V, ∀ g, e.conj (ρ g) = (χ g : k) • ρ g :=
  ρ.exists_quadratic_selfTwist_of_stableLines_orbit H hchar
    (ρ.exists_stableLines_pair_of_cyclic_quotient H hV hirr hres)

end Representation
