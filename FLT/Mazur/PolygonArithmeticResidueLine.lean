/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticBoundaryLine
public import FLT.Mazur.PolygonInfinitesimalSpecialDivisor

/-!
# The original residue boundary of the arithmetic polarization

The full arithmetic boundary restricts exactly to the original unit-one
polygon divisor. Its positive line and canonical section are retained by
the specified residue-fiber comparison, including in mixed characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules IsLocalRing
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] [IsLocalRing A] (π : A)
  (hπ : algebraMap A (ResidueField A) π = 0) (m n : ℕ) (h : 2 ≤ n)
local notation "K" => ResidueField A

/-- The original residue inclusion pulls back the entire arithmetic boundary ideal. -/
theorem boundaryIdeal_residueFiberInclusion :
    (boundaryIdeal A π m n h).comap (residueFiberInclusion A π hπ m n h) =
      PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h) (fun _ ↦ 1) := by
  have hz := PolygonInfinitesimal.markingDivisor_parameterProjection (parameter A π m) n h
    (residueMap A π hπ m) 0 (residueMap_parameter A π hπ m) (fun _ ↦ 1)
  simp only [map_one] at hz
  change (boundaryIdeal A π m n h).comap (zeroSpecialization A π hπ m n h) =
    PolygonInfinitesimal.markingDivisor K 0 n h (fun _ ↦ 1) at hz
  rw [residueFiberInclusion, Scheme.IdealSheafData.comap_comp, hz,
    PolygonInfinitesimal.markingDivisor_zeroFiberIso]

variable [NeZero n]

/-- The residue comparison of actual invertible ideals is an isomorphism. -/
instance boundaryIdeal_residue_isIso :
    IsIso (idealModulePullbackHom (boundaryIdeal A π m n h)
      (residueFiberInclusion A π hπ m n h)) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (boundaryIdeal_cartier A π m n h).1
  rw [boundaryIdeal_residueFiberInclusion]
  exact (PolygonInfinitesimalStages.specialBoundary_cartier K n h).1

/-- The actual arithmetic line restricts to the original residue polygon boundary line. -/
def boundaryLineResidueIso :
    (pullback (residueFiberInclusion A π hπ m n h)).obj (boundaryLine A π m n h) ≅
      divisorLineBundle
        (PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h) (fun _ ↦ 1))
        (PolygonInfinitesimalStages.specialBoundary_cartier K n h).1 :=
  divisorLinePullbackIsoOfEq _ (boundaryIdeal_cartier A π m n h).1
    (PolygonInfinitesimalStages.specialBoundary_cartier K n h).1
    (boundaryIdeal_residueFiberInclusion A π hπ m n h)

/-- The residue line comparison retains the canonical section of the whole boundary. -/
theorem boundaryLineResidueIso_section :
    (pullback (residueFiberInclusion A π hπ m n h)).map
        (divisorSectionMap (boundaryIdeal_cartier A π m n h).1) ≫
          (boundaryLineResidueIso A π hπ m n h).hom =
      (modulePullbackUnitIso (residueFiberInclusion A π hπ m n h)).hom ≫
        divisorSectionMap (PolygonInfinitesimalStages.specialBoundary_cartier K n h).1 :=
  divisorLinePullbackIsoOfEq_section _ (boundaryIdeal_cartier A π m n h).1
    (PolygonInfinitesimalStages.specialBoundary_cartier K n h).1
    (boundaryIdeal_residueFiberInclusion A π hπ m n h)

end FLT.Mazur.PolygonArithmeticStages
