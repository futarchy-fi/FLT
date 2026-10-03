/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteRelativeSaturation
public import FLT.LocalClassFieldTheory.AbsoluteFundamentalClass

/-!
# Fundamental classes in finite relative H2

The positive generator of the constructed degree-torsion subgroup is the
relative fundamental class. Saturation proves that it generates all of H2,
and its absolute inflation is the class with invariant positive 1/[E:K].
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) [IsGalois K E]
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C
local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(C/K) →* Gal(E/K)))

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [FiniteDimensional K E]

local notation "d" => Module.finrank K E

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

/-- The relative fundamental class, constructed before using an absolute invariant. -/
def relativeFundamentalClass : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 :=
  relativeLowerBound R S K C E 1

omit [CharP (ResidueField S) p] in
/-- Inflation identifies the relative fundamental class with the normalized absolute class. -/
theorem relativeFundamentalClass_inflation :
    (galoisMultiplicativeInflation K C E 2).hom (relativeFundamentalClass R S K C E) =
      absoluteFundamentalClass R K C p d := by
  let : NeZero d := ⟨Module.finrank_pos.ne'⟩
  change (galoisMultiplicativeInflation K C E 2).hom
    (relativeDegreeTorsionClass R S K C E (relativeRestrictionKernelEquiv d 1)) = _
  rw [relativeDegreeTorsionClass_inflation]
  change (unramifiedMultiplicativeInflation R K C 2).hom
    ((unramifiedMultiplicativeInvariant R K C).symm (zmodToRatCircle d 1)) = _
  have he : zmodToRatCircle d 1 = (↑((1 : ℚ) / d) : AddCircle (1 : ℚ)) := by
    simpa using zmodToRatCircle_intCast d 1
  rw [he]
  rfl

omit [CharZero C] in
/-- The relative fundamental class has exact additive order equal to the degree. -/
theorem relativeFundamentalClass_order :
    addOrderOf (relativeFundamentalClass R S K C E) = d := by
  rw [relativeFundamentalClass, addOrderOf_injective _ (relativeLowerBound_injective R S K C E),
    ZMod.addOrderOf_one]

omit [CharP (ResidueField R) p] in
include p in
/-- Positive rational torsion coordinates exhaust the relative cohomology group. -/
theorem relativeLowerBound_surjective :
    Function.Surjective (relativeLowerBound R S K C E) := by
  let : NeZero d := ⟨Module.finrank_pos.ne'⟩
  exact (relativeDegreeTorsionHom_surjective R S K C E p).comp
    (relativeRestrictionKernelEquiv d).surjective

omit [CharP (ResidueField R) p] in
include p in
/-- Every relative class is an integer multiple of the fundamental class. -/
theorem relativeFundamentalClass_generates
    (x : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2) :
    ∃ j : ℤ, j • relativeFundamentalClass R S K C E = x := by
  obtain ⟨z, rfl⟩ := relativeLowerBound_surjective R S K C E p x
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨j, ?_⟩
  change j • relativeLowerBound R S K C E 1 = _
  rw [← map_zsmul]
  congr 1
  simp

end LocalClassFieldTheory
