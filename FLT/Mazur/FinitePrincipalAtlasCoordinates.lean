/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasTargetCovers
public import FLT.Mazur.PrincipalAffineOpenGeometry
public import FLT.Mazur.PrincipalOccurrenceOriginalGeometry

/-!
# Base-linear coordinate equivalences for the finite occurrence atlas

The chosen finite geometric atlas supplies all the literal localization
isomorphisms required by occurrence approximation. The original incidence
squares follow from the actual sheaf restrictions, rather than extra data.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} (U : ι → X.affineOpens) (f : X ⟶ Spec R)

/-- Every chosen occurrence has actual base-linear principal coordinates. -/
def atlasPrincipalEquiv :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    ∀ i (k : AtlasPrincipalOccurrence U i),
      Localization.Away (atlasPrincipalSection U i k) ≃ₐ[R]
        Localization.Away (1 : Γ(X, (atlasPrincipalOpen U
          (atlasPrincipalDestination U i k)).1)) := by
  intro _ _ i k
  exact (principalAffineOpenEquiv f (U i)
    (atlasPrincipalOpen U (atlasPrincipalDestination U i k))
    (atlasPrincipalSection U i k) (atlasPrincipalSection_open U i k).symm).trans
      (affineOpenUnitEquiv f (atlasPrincipalOpen U (atlasPrincipalDestination U i k)))

/-- The coordinate occurrence embeddings commute with the original atlas inclusions. -/
@[reassoc] theorem atlasPrincipalEquiv_incidence (i : ι) (k : AtlasPrincipalOccurrence U i) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    principalOccurrenceOriginalOpen (R := R) (dst := atlasPrincipalDestination U)
      (a := atlasPrincipalSection U) (b := fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1)))
      (atlasPrincipalEquiv U f) i k ≫ (U i).2.fromSpec =
      affineOpenUnitChart f (atlasPrincipalOpen U (atlasPrincipalDestination U i k)) := by
  intro _ _
  let W := atlasPrincipalOpen U (atlasPrincipalDestination U i k)
  let r := atlasPrincipalSection U i k
  let he : W.1 = X.basicOpen r := (atlasPrincipalSection_open U i k).symm
  change Spec.map (CommRingCat.ofHom
      (((affineOpenUnitEquiv f W).toRingHom).comp
        (principalAffineOpenEquiv f (U i) W r he).toRingHom)) ≫
      PrincipalLocalizationSquare.inclusion r ≫ (U i).2.fromSpec = _
  rw [show CommRingCat.ofHom
      (((affineOpenUnitEquiv f W).toRingHom).comp
        (principalAffineOpenEquiv f (U i) W r he).toRingHom) =
      CommRingCat.ofHom (principalAffineOpenEquiv f (U i) W r he).toRingHom ≫
        CommRingCat.ofHom (affineOpenUnitEquiv f W).toRingHom from rfl,
    Spec.map_comp, Category.assoc, principalAffineOpenEquiv_spec]
  rfl

omit [QuasiSeparatedSpace X] in
/-- Local finite type of the scheme supplies finite type for every actual chart algebra. -/
theorem atlasChartAlgebra_finiteType [LocallyOfFiniteType f] (W : X.affineOpens) :
    let _ := chartAlgebra f W
    Algebra.FiniteType R Γ(X, W.1) := by
  change (chartScalars f W).FiniteType
  apply (f.finiteType_appLE (isAffineOpen_top _) W.2 (by simp)).comp
  exact RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.surjective

end FLT.Mazur.Approximation
