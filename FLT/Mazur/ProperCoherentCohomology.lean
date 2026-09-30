/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCohomologyWitnesses
public import FLT.Mazur.StructureCohomologyFinite

/-!
# Finite coherent cohomology for proper schemes over a field

Geometric Chow witnesses and coherent dévissage prove finiteness in every
cohomological degree. In particular, the actual structure-sheaf cohomology
and `H1` are finite-dimensional. No nonemptiness or witness assumption is needed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open FLT.Mazur.Chow

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Every coherent coefficient on a proper scheme has finite cohomology over its base field. -/
theorem proper_coherent_hasFiniteCohomology (M : X.Modules) [M.IsFinitePresentation] :
    HasFiniteCohomology f M := by
  let := source_isNoetherian f
  exact coherent_hasFiniteCohomology_of_witnesses f (proper_hasGenericRankOneWitnesses f) M

/-- Actual structure-sheaf cohomology of a proper scheme is finite-dimensional in every degree. -/
theorem finiteDimensional_scalarH_of_proper (q : ℕ) :
    FiniteDimensional k (ScalarH f q) := by
  let := source_isNoetherian f
  exact finiteDimensional_scalarH_of_witnesses f (proper_hasGenericRankOneWitnesses f) q

/-- Properness implies finite-dimensionality of the actual first structure-sheaf cohomology. -/
theorem finiteDimensional_H1_of_proper : FiniteDimensional k (H1 f) :=
  finiteDimensional_scalarH_of_proper f 1

end FLT.Mazur.FCurve
