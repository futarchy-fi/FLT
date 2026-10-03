/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FiniteFlatCyclotomicRestriction
public import FLT.Deformations.RepresentationTheory.FlatDiscrete
public import FLT.Deformations.RepresentationTheory.IteratedBaseChangeIrreducible
public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop

/-!
# Absolute irreducibility on the cyclotomic kernel

Apply the same-generator obstruction over each extended field's algebraic
closure, cancel iterated base change, and descend irreducibility. The result
uses the repository's predicate quantifying over all coefficient extensions.
-/

@[expose] public noncomputable section
universe u
namespace GaloisRep
open NumberField

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p

/-- The large-prime finite-flat representation stays absolutely irreducible on the kernel. -/
theorem flat_cyclotomic_restriction_absolute {k V : Type} [Field k] [TopologicalSpace k]
    [CharP k p] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : GaloisRep ℚ k V) (hp : 3 < p)
    (hflat : ρ.HasFlatProlongationAt v) (hdim : Module.finrank k V = 2)
    (hdet : ∀ g, (ρ g).det = ZMod.castHom (dvd_refl p) k (CyclotomicQuadratic.character p g))
    (habs : ρ.toRepresentation.IsAbsolutelyIrreducible.{u}) :
    Representation.IsAbsolutelyIrreducible.{u}
      (ρ.toRepresentation.comp (CyclotomicQuadratic.character p).ker.subtype) := by
  constructor
  intro E _ _
  let L := AlgebraicClosure E
  have hirr := habs.absolutelyIrreducible L inferInstance inferInstance
  have hres := ρ.flat_cyclotomic_restriction_baseChange p hp hflat hdim hdet L hirr
  let τ := ρ.toRepresentation.comp (CyclotomicQuadratic.character p).ker.subtype
  have hiter : (Representation.baseChange L (Representation.baseChange E τ)).IsIrreducible :=
    (Representation.isIrreducible_baseChange_tower_iff τ E L).mpr hres
  exact Slop.OddRep.isIrreducible_of_baseChange (Representation.baseChange E τ) L hiter

/-- Discrete flatness supplies the model required by the absolute restriction theorem. -/
theorem flat_cyclotomic_restriction_absolute_of_isFlatAt
    {k V : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [DiscreteTopology k]
    [CharP k p] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : GaloisRep ℚ k V) (hp : 3 < p)
    (hflat : ρ.IsFlatAt v) (hdim : Module.finrank k V = 2)
    (hdet : ∀ g, (ρ g).det = ZMod.castHom (dvd_refl p) k (CyclotomicQuadratic.character p g))
    (habs : ρ.toRepresentation.IsAbsolutelyIrreducible.{u}) :
    Representation.IsAbsolutelyIrreducible.{u}
      (ρ.toRepresentation.comp (CyclotomicQuadratic.character p).ker.subtype) :=
  ρ.flat_cyclotomic_restriction_absolute p hp
    ((ρ.isFlatAt_iff_hasFlatProlongationAt v).mp hflat) hdim hdet habs

end GaloisRep
