/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartRefinementNaturality

/-!
# Affine faithfully flat charts and their geometric refinements

A chart records only rings, scheme maps, and the faithfully flat cover square.
Refinements record its factorizations. Effective descent constructs the module
sheaves and comparison isomorphisms from these geometric inputs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- A faithfully flat affine chart square over a scheme cover. -/
structure Chart where
  /-- Ring of the base chart. -/
  baseRing : CommRingCat.{u}
  /-- Ring of the covering chart. -/
  coverRing : CommRingCat.{u}
  /-- The affine cover map in ring coordinates. -/
  ringMap : baseRing ⟶ coverRing
  /-- The chosen affine cover is faithfully flat. -/
  faithfullyFlat : ringMap.hom.FaithfullyFlat
  /-- Map of the affine base chart into the base scheme. -/
  base : Spec baseRing ⟶ X
  /-- Map of the affine covering chart into the covering scheme. -/
  cover : Spec coverRing ⟶ Y
  /-- The chart lies over the original scheme cover. -/
  square : Spec.map ringMap ≫ base = cover ≫ p

namespace Chart
variable {p} (C C' : Chart p)

/-- Geometric factorization of one faithfully flat affine chart through another. -/
structure Refinement where
  /-- Map of base coordinate rings. -/
  base : C.baseRing ⟶ C'.baseRing
  /-- Map of covering coordinate rings. -/
  cover : C.coverRing ⟶ C'.coverRing
  /-- The affine refinement square commutes. -/
  square : C.ringMap ≫ cover = base ≫ C'.ringMap
  /-- Factorization of the named base chart. -/
  base_over : Spec.map base ≫ C.base = C'.base
  /-- Factorization of the named covering chart. -/
  cover_over : Spec.map cover ≫ C.cover = C'.cover

variable {M N : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (E : SchemeGeometricDescent.Data p N)
variable [((pullback C.cover).obj M).IsQuasicoherent]

/-- The effectively descended sheaf of the chosen affine chart. -/
def sheaf : (Spec C.baseRing).Modules :=
  D.chartSheaf C.ringMap p C.base C.cover C.square C.faithfullyFlat

instance sheaf_isQuasicoherent : (C.sheaf D).IsQuasicoherent :=
  inferInstanceAs (D.chartSheaf C.ringMap p C.base C.cover C.square
    C.faithfullyFlat).IsQuasicoherent

/-- The chart sheaf reconstructs the original sheaf on the covering chart. -/
def reconstruction : (pullback (Spec.map C.ringMap)).obj (C.sheaf D) ≅
    (pullback C.cover).obj M :=
  D.chartReconstruction C.ringMap p C.base C.cover C.square C.faithfullyFlat

variable [((pullback C.cover).obj N).IsQuasicoherent]

/-- Effective descent of a compatible original scheme map on this chart. -/
def map (f : M ⟶ N) (hf : D.MapCompatible p E f) : C.sheaf D ⟶ C.sheaf E :=
  D.chartMap C.ringMap p E C.base C.cover C.square C.faithfullyFlat f hf

variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable (ρ : C.Refinement C')

/-- The actual comparison to a geometrically refined chart. -/
def comparison : (pullback (Spec.map ρ.base)).obj (C.sheaf D) ≅ C'.sheaf D :=
  D.chartRefinementIsoTo C.ringMap C'.ringMap ρ.base ρ.cover ρ.square p
    C.base C.cover C.square C.faithfullyFlat C'.faithfullyFlat C'.base C'.cover
    ρ.base_over ρ.cover_over C'.square

variable [((pullback C'.cover).obj N).IsQuasicoherent]

/-- Chart comparison is natural for maps compatible with the original scheme datum. -/
@[reassoc]
theorem comparison_naturality (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (pullback (Spec.map ρ.base)).map (C.map D E f hf) ≫ (C.comparison C' E ρ).hom =
      (C.comparison C' D ρ).hom ≫ C'.map D E f hf :=
  D.chartRefinementIsoTo_naturality C.ringMap C'.ringMap ρ.base ρ.cover ρ.square p E
    C.base C.cover C.square C.faithfullyFlat C'.faithfullyFlat C'.base C'.cover
    ρ.base_over ρ.cover_over C'.square f hf

end Chart
end FLT.Mazur.SchemeAffineDescent
