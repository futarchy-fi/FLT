/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingBranchSwapGeometry

/-!
# Full branch interchange commutes with coefficient restriction

Both generators and every coefficient are preserved through the oriented
comparison, including at nonreduced arithmetic orders.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) (hs : f t = s)

/-- Coefficient substitution commutes with the full coordinate interchange. -/
theorem ringMap_branchSwap :
    (branchSwapMap s).toRingHom.comp (ringMap f t s hs) =
      (ringMap f t s hs).comp (branchSwapMap t).toRingHom := by
  subst s
  let _ := f.toAlgebra
  change (branchSwapMap (algebraMap R S t)).toRingHom.comp
    (ringMap (algebraMap R S) t (algebraMap R S t) rfl) =
      (ringMap (algebraMap R S) t (algebraMap R S t) rfl).comp _
  rw [ringMap_eq_coefficientMap]
  have he : ((branchSwapMap (algebraMap R S t)).restrictScalars R).comp
      (coefficientAlgHom R S t) =
        (coefficientAlgHom R S t).comp (branchSwapMap t) := by
    apply chartRing_hom_ext t <;> simp
  exact congrArg AlgHom.toRingHom he

/-- The actual oriented node scheme commutes with the original coefficient map. -/
@[reassoc] theorem branchSwapIso_ringMap :
    (branchSwapIso S s).hom ≫ Spec.map (CommRingCat.ofHom (ringMap f t s hs)) =
      Spec.map (CommRingCat.ofHom (ringMap f t s hs)) ≫ (branchSwapIso R t).hom := by
  change Spec.map (CommRingCat.ofHom (branchSwapMap s).toRingHom) ≫ Spec.map _ =
    Spec.map _ ≫ Spec.map (CommRingCat.ofHom (branchSwapMap t).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (ringMap_branchSwap f t s hs))

end FLT.Mazur.PolygonSmoothing
