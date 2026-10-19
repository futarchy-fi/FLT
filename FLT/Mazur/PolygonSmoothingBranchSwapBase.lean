/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingBranchSwapGeometry
public import FLT.Mazur.PolygonSmoothingSpecialFiber

/-!
# Branch interchange over the full coefficient base

Interchanging the two node coordinates fixes every coefficient, including
nilpotents. Thus the entire node involution is an isomorphism over the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
variable (R : Type*) [CommRing R] (t : R)

/-- The full coordinate interchange preserves the original coefficient projection. -/
@[reassoc] theorem branchSwapIso_base :
    (branchSwapIso R t).hom ≫ chartStructure R t = chartStructure R t := by
  change Spec.map (CommRingCat.ofHom (branchSwapMap t).toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fun r ↦ (branchSwapMap t).commutes r))

/-- The whole branch interchange is an automorphism over the coefficient scheme. -/
def branchSwapOver : Over.mk (chartStructure R t) ≅ Over.mk (chartStructure R t) :=
  Over.isoMk (branchSwapIso R t) (branchSwapIso_base R t)

end FLT.Mazur.PolygonSmoothing
