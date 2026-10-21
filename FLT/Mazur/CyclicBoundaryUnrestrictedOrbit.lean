/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryGroupSections
public import FLT.Mazur.CyclicMarkingSingularLocus

/-!
# The full orbit equation on the unrestricted boundary parameter scheme

The actual parameter scheme retains both auxiliary markings and every cyclic
marking, including collisions. Its full universal orbit defines a closed
multiplication locus without restricting the parameter to the faithful open.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
local notation "B" => parameter E.group n

/-- The full original generalized curve over the unrestricted boundary parameter. -/
def unrestrictedUniversalCurve : GeneralizedEllipticCurve (B).left := E.baseChange (B).hom

/-- The actual cyclic factor of the universal boundary marking. -/
def unrestrictedUniversalMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over (B).left) ⟶ (unrestrictedUniversalCurve E n).group) :=
  cyclicSectionMarking E.group n (B).hom (𝟙 (B))

variable [SmoothOfRelativeDimension 1 E.group.hom]

instance unrestrictedUniversalCurve_group_smooth :
    SmoothOfRelativeDimension 1 (unrestrictedUniversalCurve E n).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom
    (B).hom inferInstance

/-- The universal full orbit has degree n even at repeated labels and singular fibers. -/
theorem unrestrictedUniversalOrbit_degree :
    FCurve.FiniteLocallyFreeDegree
      ((unrestrictedUniversalCurve E n).singularOrbitCarrier
        (unrestrictedUniversalMarking E n)).hom n :=
  (unrestrictedUniversalCurve E n).cyclicMarkingGroupIdeal_degree _

/-- The actual global coefficient ideal on the unrestricted boundary parameter scheme. -/
def unrestrictedMultiplicationCoefficientIdeal : (B).left.IdealSheafData :=
  (unrestrictedUniversalCurve E n).singularOrbitCoefficientIdeal (unrestrictedUniversalMarking E n)

/-- The closed equation locus inside the original unrestricted parameter scheme. -/
def unrestrictedMultiplicationLocus : Scheme :=
  (unrestrictedUniversalCurve E n).singularOrbitLocus (unrestrictedUniversalMarking E n)

/-- The original immersion of the full multiplication equation locus. -/
def unrestrictedMultiplicationLocusInclusion : unrestrictedMultiplicationLocus E n ⟶ (B).left :=
  (unrestrictedUniversalCurve E n).singularOrbitLocusInclusion (unrestrictedUniversalMarking E n)

instance unrestrictedMultiplicationLocusInclusion_closed :
    IsClosedImmersion (unrestrictedMultiplicationLocusInclusion E n) :=
  singularOrbitLocusInclusion_closed _ _

/-- Every scheme test factors through this locus exactly when its actual orbit is a subgroup. -/
theorem unrestrictedMultiplicationLocus_factorization_iff_subgroup
    {T : Scheme} (f : T ⟶ (B).left) :
    (∃ k : T ⟶ unrestrictedMultiplicationLocus E n,
      k ≫ unrestrictedMultiplicationLocusInclusion E n = f) ↔
      ∃ H : ((unrestrictedUniversalCurve E n).baseChange f).FiniteSubgroup n,
        H.ideal = ((unrestrictedUniversalCurve E n).baseChange f).cyclicMarkingIdeal
          (pullCyclicMarking f (unrestrictedUniversalMarking E n)) :=
  (unrestrictedUniversalCurve E n).singularOrbitLocus_factorization_iff_subgroup
    (unrestrictedUniversalMarking E n) f

end FLT.Mazur.CyclicBoundaryParameter
