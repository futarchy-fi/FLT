/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularLocus
public import FLT.Mazur.CyclicMarkingSingularGenerator

/-!
# The actual cyclic subgroup over the closed multiplication locus

The identity test of the constructed closed locus kills its full equation.
This constructs its universal subgroup and original Cartier generator.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "l" => E.singularOrbitLocusInclusion φ
local notation "C" => E.baseChange (l)
local notation "ψ" => pullCyclicMarking (E := E) (l) φ

local instance singularLocusSubgroup_smooth : SmoothOfRelativeDimension 1 (C).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom (l)
    inferInstance

omit [NeZero n] in
/-- The original universal equation vanishes over its constructed closed locus. -/
theorem singularOrbitLocus_multiplication :
    ClosedGroupIdeal.multiplicationEquation (C).group ((C).cyclicMarkingGroupIdeal (ψ)) = 0 :=
  (E.singularOrbitLocus_factorization_iff φ (l)).mp ⟨𝟙 _, Category.id_comp _⟩

/-- The actual cyclic subgroup on the whole curve over the multiplication locus. -/
def singularOrbitLocusSubgroup : (C).FiniteSubgroup n :=
  (C).singularCyclicDivisorSubgroup (ψ) (E.singularOrbitLocus_multiplication φ)

/-- The constructed universal subgroup retains the exact whole-curve orbit ideal. -/
theorem singularOrbitLocusSubgroup_ideal :
    (E.singularOrbitLocusSubgroup φ).ideal = (C).cyclicMarkingIdeal (ψ) :=
  (C).singularCyclicDivisorSubgroup_ideal _ _

/-- Its generator is the original residue-one cyclic label lifted through the full subgroup. -/
def singularOrbitLocusGenerator : 𝟙_ (Over (E.singularOrbitLocus φ)) ⟶
    (E.singularOrbitLocusSubgroup φ).carrier :=
  (C).singularCyclicDivisorGenerator (ψ) (E.singularOrbitLocus_multiplication φ)

/-- The universal generator retains all multiplicities in its Cartier orbit. -/
theorem singularOrbitLocusGenerator_cartier :
    (E.singularOrbitLocusSubgroup φ).IsCartierGenerator (E.singularOrbitLocusGenerator φ) :=
  (C).singularCyclicDivisorGenerator_cartier _ _

/-- The universal subgroup is cyclic without an etale or faithful-marking restriction. -/
theorem singularOrbitLocusSubgroup_isCyclic : (E.singularOrbitLocusSubgroup φ).IsCyclic :=
  (C).singularCyclicDivisorSubgroup_isCyclic _ _

end FLT.Mazur.GeneralizedEllipticCurve
