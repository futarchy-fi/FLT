/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.QuadraticRootBranchLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Simple roots give actual open charts in quadratic spectra

The explicit root evaluation factors through the principal localization
isomorphism. Thus its spectrum is an open immersion over the original base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.QuadraticRootBranchLocalization
variable {R : Type*} [CommRing R] (a b r : R)
  (hr : r ^ 2 + a * r = b) (hu : IsUnit (r + r + a))

/-- The actual root section of the original quadratic spectrum. -/
def branchChart : Spec (.of R) ⟶ Spec (.of (AdjoinRoot (polynomial a b))) :=
  Spec.map (CommRingCat.ofHom (evaluation a b r hr).toRingHom)

/-- Root evaluation is the whole principal branch, with its explicit inverse. -/
theorem branchChart_factor : branchChart a b r hr =
    Spec.map (CommRingCat.ofHom (branchEquiv a b r hr hu).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (AdjoinRoot (polynomial a b)) (Branch a b r))) := by
  rw [branchChart, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (branchEvaluation_base a b r hr hu z).symm

include hu in
/-- A simple root identifies an actual open subscheme, even over a nonreduced ring. -/
theorem branchChart_isOpenImmersion : IsOpenImmersion (branchChart a b r hr) := by
  rw [branchChart_factor a b r hr hu]
  have he : IsIso (CommRingCat.ofHom (branchEquiv a b r hr hu).toRingHom) :=
    (branchEquiv a b r hr hu).toRingEquiv.toCommRingCatIso.isIso_hom
  infer_instance

/-- The branch identification retains the exact coefficient morphism. -/
@[reassoc] theorem branchChart_structure :
    branchChart a b r hr ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot (polynomial a b)))) = 𝟙 _ := by
  rw [branchChart, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact (evaluation a b r hr).comp_algebraMap

end FLT.Mazur.QuadraticRootBranchLocalization
