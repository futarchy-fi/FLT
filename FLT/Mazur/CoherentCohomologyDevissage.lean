/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentCohomologyFinite
public import FLT.Mazur.CoherentGenericRankOneCriterion

/-!
# Finite cohomology from generic-rank-one witnesses

Specialize coherent dévissage to all-degree scalar cohomology finiteness.
The zero coefficient has finite cohomology, so no nonemptiness assumption is
needed. The geometric existence of the witnesses remains an explicit input;
this file does not prove proper coherent cohomology finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry ZeroObject
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.FCurve

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- On an empty scheme every coefficient has finite cohomology, without a witness
or coherence assumption. -/
theorem hasFiniteCohomology_of_isEmpty [IsEmpty X] (M : X.Modules) :
    HasFiniteCohomology f M :=
  hasFiniteCohomology_of_isZero f M
    ((isZero_iff_stalk_isZero M).mpr (fun x ↦ isEmptyElim x))

/-- The original integral-closed-subscheme witness hypothesis implies finite
cohomology for every coherent coefficient, including on an empty scheme. -/
theorem coherent_hasFiniteCohomology_of_witnesses [IsNoetherian X]
    (hw : HasGenericRankOneWitnesses (HasFiniteCohomology f))
    (M : X.Modules) [M.IsFinitePresentation] : HasFiniteCohomology f M :=
  generic_rank_one_of_zero (hasFiniteCohomology_twoOutOfThree f) hw
    (hasFiniteCohomology_of_isZero f 0 (isZero_zero _)) M

end FLT.Mazur.FCurve
