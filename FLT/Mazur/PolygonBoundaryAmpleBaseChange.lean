/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryAmpleParameter
public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeModuli

/-!
# Actual ample polygon charts over arbitrary base schemes

The split polygon's ample parameter scheme commutes with every base morphism,
including nonfield and nonreduced bases. The full original parameter subgroup
and modular transformation are retained, for independent polygon size and rank.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonBoundaryModuli CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (m : ℕ) [NeZero m] (n : ℕ) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "E" => boundaryCurve K m
local notation "B" => cyclicFaithfulParameter (GeneralizedEllipticCurve.group (E)) n

local instance polygonAmplePullbackGroup_separated :
    IsSeparated ((E).baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (E).group.hom g))

local instance polygonAmplePullbackGroup_smooth :
    SmoothOfRelativeDimension 1 ((E).baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) (E).group.hom g
    inferInstance

/-- The actual split-polygon ample chart commutes with arbitrary, possibly nonfield base change. -/
def ampleBoundaryBaseChangeIso :
    pullback (ampleParameterBase (E) n) g ≅ ampleParameter ((E).baseChange g) n :=
  ampleBaseChangeIso g (E) n

/-- The chart comparison retains the original ample polygon parameter. -/
@[reassoc] theorem ampleBoundaryBaseChangeIso_original :
    (ampleBoundaryBaseChangeIso K m n g).hom ≫ ampleBaseChangeToOriginal g (E) n =
      pullback.fst (ampleParameterBase (E) n) g :=
  ampleBaseChangeIso_hom_original g (E) n

/-- The new universal subgroup is the actual pullback of the original polygon parameter subgroup. -/
def ampleBoundaryBaseChangeParameterSubgroupIso :
    CompatibleIso (ampleUniversalLevel ((E).baseChange g) n).val.2
      ((parameterSubgroup K m (NeZero.pos m) (PolygonAtlas.normalization K m)
        (PolygonAtlas.nodes K m) (PolygonAtlas.isPushout K m (NeZero.pos m)) n
        (B).hom (cyclicFaithfulInclusion (E).group n)
        (faithfulUniversalMarking_distinct (E) n)).baseChange
          (ampleBaseChangeToOriginal g (E) n ≫ (ampleParameterOpen (E) n).ι)) := by
  let c := faithfulBaseChangeTestSubgroupIso g (E) n (ampleParameterOpen ((E).baseChange g) n).ι
  rw [← ampleBaseChangeToOriginal_inclusion g (E) n] at c
  exact c

/-- Every new-base polygon test has exactly the original boundary chart's modular class. -/
theorem ampleBoundaryModuliMap_baseChange :
    ampleModuliMap ((E).baseChange g) n =
      uliftYoneda.map (ampleBaseChangeToOriginal g (E) n) ≫ ampleBoundaryModuliMap K m n :=
  ampleModuliMap_baseChange g (E) n

end FLT.Mazur.PolygonCyclicBoundary
