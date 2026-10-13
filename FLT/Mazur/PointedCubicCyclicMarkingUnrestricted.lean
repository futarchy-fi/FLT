/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCyclicMarkingTransport
public import FLT.Mazur.PointedCubicSubgroupTransportUnrestricted

/-!
# The original cyclic marking in a full pointed cubic chart

These results hold over arbitrary bases, without Noetherian assumptions.
The full homomorphism is transported through the proved original DR comparison.
The subgroup reconstructed from these sections remains compatibly isomorphic to
the original subgroup, and every section projects through the given curve map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart UniversallyDistinctSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsAffine S]
  (E : GeneralizedEllipticCurve S) (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (e : E.curve.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = E.curve.hom ≫ S.toSpecΓ)
  (hs : E.identitySection.left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W)
  {n : ℕ} (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- All original cyclic labels in the established cubic family. -/
def pointedCubicMarkingUnrestricted :
    Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group) :=
  transportCyclicMarking (pointedCubicFamilyIsoUnrestricted W E e he hs) φ

/-- Projection of every transported section is its original complete cubic image. -/
@[reassoc] theorem pointedCubicMarking_fst_unrestricted (i : Multiplicative (ZMod n)) :
    (pointedCubicMarkingUnrestricted E W e he hs φ i).left ≫
      pullback.fst (integralCurveStructure W) S.toSpecΓ =
        (φ i).left ≫ E.inclusion.left ≫ e.hom := by
  change ((φ i) ≫ (pointedCubicGroupIso E W e he).hom).left ≫ _ = _
  rw [Over.comp_left, Category.assoc, pointedCubicGroupIso_fst]

/-- The full original cyclic marking stays universally distinct in the cubic chart. -/
theorem pointedCubicMarking_distinct_unrestricted
    (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i))) :
    UniversallyDistinct (fun i : ZMod n ↦ pointedCubicMarkingUnrestricted E W e he hs φ (.ofAdd
      i)) :=
  (transportCyclicMarking_distinct_iff (pointedCubicFamilyIsoUnrestricted W E e he hs) φ).mpr hφ

variable [NeZero n] (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  (H : E.FiniteSubgroup n) (a : FiniteSubgroup.CompatibleIso (E.relativeCyclicSubgroup φ hφ) H)

/-- Reconstruction in the actual cubic chart retains the originally specified subgroup. -/
def pointedCubicMarkingOriginalIsoUnrestricted :
    FiniteSubgroup.CompatibleIso
      ((pointedCubicFamily W).relativeCyclicSubgroup (pointedCubicMarkingUnrestricted E W e he hs
        φ)
        (pointedCubicMarking_distinct_unrestricted E W e he hs φ hφ)) H :=
  transportCyclicMarkingOriginalIso (pointedCubicFamilyIsoUnrestricted W E e he hs) φ hφ H a

end FLT.Mazur.GeneralizedEllipticCurve
