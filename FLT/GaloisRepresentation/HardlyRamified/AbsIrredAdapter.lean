/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.Deformations.RepresentationTheory.Irreducible
public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop

/-!
# Absolute irreducibility from a rank-one fixed space

Package irreducibility after every field extension into the class used by
`Deformation.isCorepresentable_deformationFunctor` and
`MoritaReconstruction.exists_universalTraceLift`. The fixed-space hypothesis
is explicit; obtaining it from complex conjugation is a separate step.
-/

@[expose] public section

universe u

namespace Representation

/-- An irreducible representation with a one-dimensional fixed space for some
group element is absolutely irreducible in the sense used by deformation theory. -/
theorem absIrred_of_rank_one_fixed_space
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V)
    (hirr : ρ.IsIrreducible) {c : G}
    (hc : Module.finrank k (Module.End.eigenspace (ρ c) 1) = 1) :
    ρ.IsAbsolutelyIrreducible.{u} := by
  constructor
  intro l _ _
  exact Slop.OddRep.isIrreducible_baseChange_of_finrank_eigenspace_eq_one ρ l hirr hc

end Representation

namespace GaloisRep

/-- The absolute-irreducibility adapter for Galois representations, with the
rank-one fixed-space condition retained as an explicit hypothesis. -/
theorem absIrred_of_rank_one_fixed_space
    {K k V : Type*} [Field K] [Field k] [TopologicalSpace k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : GaloisRep K k V) (hirr : ρ.IsIrreducible)
    {c : Field.absoluteGaloisGroup K}
    (hc : Module.finrank k (Module.End.eigenspace (ρ c) 1) = 1) :
    ρ.toRepresentation.IsAbsolutelyIrreducible.{u} :=
  Representation.absIrred_of_rank_one_fixed_space ρ.toRepresentation hirr hc

end GaloisRep
