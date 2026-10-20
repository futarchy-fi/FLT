/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleModuli
public import FLT.Mazur.PolygonBoundaryCyclicSubgroup
public import FLT.Mazur.PolygonBoundaryModuliMap

/-!
# Ample cyclic parameter opens for every split polygon

The cyclic rank is independent of the polygon size. The universal subgroup is
exactly the previously constructed parameter subgroup on the full original polygon.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonBoundaryModuli CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (m : ℕ) [NeZero m]
local notation "E" => boundaryCurve K m
local notation "p" => PolygonAtlas.normalization K m
local notation "q" => PolygonAtlas.nodes K m
local notation "h" => PolygonAtlas.isPushout K m (NeZero.pos m)

instance splitBoundaryGroup_separated : IsSeparated (G K m).hom := by
  change IsSeparated (E).group.hom
  let _ := (E).family.family.1
  rw [← (E).inclusion.w]
  infer_instance

instance splitBoundaryGroup_relativeDimension : SmoothOfRelativeDimension 1 (G K m).hom :=
  boundaryGroup_relativeDimension K m (NeZero.pos m) p q h

instance canonicalBoundaryGroup_separated : IsSeparated (E).group.hom :=
  splitBoundaryGroup_separated K m

instance canonicalBoundaryGroup_relativeDimension :
    SmoothOfRelativeDimension 1 (E).group.hom := splitBoundaryGroup_relativeDimension K m

variable (n : ℕ) [NeZero n]
local notation "P" => cyclicFaithfulParameter (G K m) n

/-- The universal subgroup is the unchanged original boundary parameter subgroup. -/
theorem faithfulUniversalSubgroup_eq_parameterSubgroup :
    faithfulUniversalSubgroup (E) n =
      parameterSubgroup K m (NeZero.pos m) p q h n (P).hom
        (cyclicFaithfulInclusion (G K m) n) (faithfulUniversalMarking_distinct (E) n) := rfl

/-- The constructed ample cyclic parameter scheme for the entire split m-gon. -/
def ampleBoundaryParameter : Scheme := ampleParameter (E) n

/-- Its actual open inclusion in the original boundary marking parameter. -/
def ampleBoundaryParameterInclusion : ampleBoundaryParameter K m n ⟶ (parameter (G K m) n).left :=
  ampleParameterInclusion (E) n

instance ampleBoundaryParameterInclusion_isOpenImmersion :
    IsOpenImmersion (ampleBoundaryParameterInclusion K m n) :=
  ampleParameterInclusion_isOpenImmersion (E) n

/-- The original full polygon and subgroup define the boundary modular transformation. -/
def ampleBoundaryModuliMap : uliftYoneda.{1}.obj (ampleBoundaryParameter K m n) ⟶
    GeneralizedEllipticCurve.FiniteSubgroup.ampleCyclicClassPresheaf n := ampleModuliMap (E) n

/-- Ampleness of every test of the original universal subgroup is represented by this open. -/
theorem ampleBoundaryParameter_criterion {T : Scheme} (g : T ⟶ (P).left) :
    ((faithfulUniversalSubgroup (E) n).baseChange g).IsAmple ↔
      ∃! v : T ⟶ ampleBoundaryParameter K m n, v ≫ (ampleParameterOpen (E) n).ι = g :=
  ampleParameter_criterion (E) n g

end FLT.Mazur.PolygonCyclicBoundary
