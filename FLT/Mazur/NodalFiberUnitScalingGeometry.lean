/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberUnitScalingNaturality
public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Natural full-node isomorphisms for unit-normalized smoothing

The complete scheme comparison preserves the base and follows any coefficient
map preserving the specified unit factors. Neither puncture is removed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (c t : R) (u : Rˣ) (hc : c = t * ↑u)

/-- The complete unit-normalized node is the entire polygon smoothing chart. -/
def unitSmoothingIso : Spec (.of (Coordinate c)) ≅ PolygonSmoothing.chart R t :=
  (Scheme.Spec.mapIso (unitSmoothingEquiv c t u hc).toRingEquiv.toCommRingCatIso.op).symm

/-- The full scheme comparison retains the original base structure. -/
@[reassoc] theorem unitSmoothingIso_structure :
    (unitSmoothingIso c t u hc).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing t))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate c))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (unitSmoothingEquiv c t u hc).symm.toAlgHom.comp_algebraMap

variable {S : Type u} [CommRing S] (f : R →+* S)
  (d s : S) (v : Sˣ) (hd : d = s * ↑v)
  (hcd : f c = d) (hts : f t = s) (huv : f (u : R) = (v : S))

include huv in
/-- Both entire node charts commute with the specified coefficient substitution. -/
@[reassoc] theorem unitSmoothingIso_coefficients :
    Spec.map (CommRingCat.ofHom (coefficientRingMap f c d hcd)) ≫
      (unitSmoothingIso c t u hc).hom =
        (unitSmoothingIso d s v hd).hom ≫
          Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap f t s hts)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact unitSmoothingEquiv_symm_coefficients f c t d s u v hc hd hcd hts huv

end FLT.Mazur.NodalFiber
