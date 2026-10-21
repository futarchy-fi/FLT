/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDifferentialOpenLift

/-!
# Naturality of the full original differential open

The constructed differential open pulls back exactly along arbitrary test
maps. Its actual scheme restrictions preserve the comparison equation, so
full arrows agree under refinement and across infinitesimal stage maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B V : Scheme.{0}} {p q : D ⟶ A} (J : A.IdealSheafData)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
attribute [local irreducible] scalarMorphism

/-- The full differential open commutes with every change of coefficient test. -/
theorem originalBoundary_differentialOpen_precompose (t : B ⟶ pullback f f) (u : V ⟶ B) :
    originalBoundaryDifferentialOpen J (u ≫ t) = u ⁻¹ᵁ originalBoundaryDifferentialOpen J t := by
  simp only [originalBoundaryDifferentialOpen, PrincipalIdealComparisonLift.idealOpen,
    Scheme.Hom.preimage_iSup, Scheme.preimage_basicOpen_top, Category.assoc,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]

/-- The actual restricted test map on the constructed differential opens. -/
def originalBoundaryDifferentialOpenMap (t : B ⟶ pullback f f) (u : V ⟶ B) :
    (originalBoundaryDifferentialOpen J (u ≫ t)).toScheme ⟶
      (originalBoundaryDifferentialOpen J t).toScheme :=
  u.resLE _ _ (originalBoundary_differentialOpen_precompose J t u).le

/-- This restriction preserves the full coefficient map, not only its point set. -/
@[reassoc]
theorem originalBoundaryDifferentialOpenMap_ι (t : B ⟶ pullback f f) (u : V ⟶ B) :
    originalBoundaryDifferentialOpenMap J t u ≫ (originalBoundaryDifferentialOpen J t).ι =
      (originalBoundaryDifferentialOpen J (u ≫ t)).ι ≫ u :=
  Scheme.Hom.resLE_comp_ι _ _

variable (e : CategoryTheory.EquivalenceRelation p q)
  (hJ : J.comap p = J.comap q)
local notation "c" => originalBoundaryComparison p q J hJ

include e

/-- Full original arrows on the differential opens are automatically natural under test maps. -/
theorem originalBoundary_differentialOpen_lift_natural
    (t : B ⟶ pullback f f) (u : V ⟶ B)
    (d : (originalBoundaryDifferentialOpen J t).toScheme ⟶ pullback p J.subschemeι)
    (d' : (originalBoundaryDifferentialOpen J (u ≫ t)).toScheme ⟶ pullback p J.subschemeι)
    (hd : d ≫ c = (originalBoundaryDifferentialOpen J t).ι ≫ t)
    (hd' : d' ≫ c = (originalBoundaryDifferentialOpen J (u ≫ t)).ι ≫ (u ≫ t)) :
    originalBoundaryDifferentialOpenMap J t u ≫ d = d' := by
  let _ := originalBoundaryComparison_mono e J hJ
  apply (cancel_mono c).mp
  rw [Category.assoc, hd, ← Category.assoc, originalBoundaryDifferentialOpenMap_ι,
    Category.assoc, hd']

end FLT.Mazur.EquivalenceRelationOrderedFrames
