/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentCohomologyDevissage
public import FLT.Mazur.CoherentFreeSheaf

/-!
# Structure-sheaf finiteness from coherent dévissage witnesses

The structure coefficient is coherent, and its module cohomology is linearly
isomorphic to the actual scalar structure-sheaf cohomology. Thus D19's witness
hypothesis suffices for finite-dimensionality of `ScalarH`, in particular `H1`.
The witnesses are still an input: proper finiteness and genus require their
geometric construction and are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.FCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Generic-rank-one finite-cohomology witnesses imply finite-dimensionality of
actual structure-sheaf cohomology in every degree. -/
theorem finiteDimensional_scalarH_of_witnesses
    (hw : HasGenericRankOneWitnesses (HasFiniteCohomology f)) (n : ℕ) :
    FiniteDimensional k (ScalarH f n) := by
  let : Module.Finite k (ModuleScalarH f (structureUnitModule X) n) :=
    coherent_hasFiniteCohomology_of_witnesses f hw (structureUnitModule X) n
  exact Module.Finite.equiv (moduleScalarHUnitEquiv f n)

/-- The degree-one specialization retains the unproved geometric witness obligation. -/
theorem finiteDimensional_H1_of_witnesses
    (hw : HasGenericRankOneWitnesses (HasFiniteCohomology f)) :
    FiniteDimensional k (H1 f) :=
  finiteDimensional_scalarH_of_witnesses f hw 1

end FLT.Mazur.FCurve
