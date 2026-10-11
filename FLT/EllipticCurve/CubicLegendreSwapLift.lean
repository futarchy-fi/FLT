/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicRingMaps
/-! # The parameter swap on its actual quadratic cover

The map λ ↦ 1-λ lifts to the standard étale root cover while fixing √(-1).
Its square is identity. Combining this coefficient map with the actual
swap coordinate change gives an involutive automorphism of the cyclic scheme
over the cover, with the stated action on its coefficient base.

The comparison with the previously descended global swap automorphism
remains to be proved; the local square identity alone does not establish it.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lift a coefficient ring map using a specified unit square root. -/
def quadraticUnitRingLift (f : R →+* S) (d : Rˣ) (r : Sˣ)
    (h2 : IsUnit (2 : S)) (hr : (r : S) ^ 2 = f d) :
    QuadraticEtaleRing d →+* S := by
  letI : Algebra R S := f.toAlgebra
  exact (quadraticUnitLift d r h2 hr).toRingHom

theorem quadraticUnitRingLift_root (f : R →+* S) (d : Rˣ) (r : Sˣ)
    (h2 : IsUnit (2 : S)) (hr : (r : S) ^ 2 = f d) :
    quadraticUnitRingLift f d r h2 hr (quadraticEtaleUnit d) = r := by
  let : Algebra R S := f.toAlgebra
  exact quadraticUnitLift_unit d r h2 hr

theorem quadraticUnitRingLift_scalar (f : R →+* S) (d : Rˣ) (r : Sˣ)
    (h2 : IsUnit (2 : S)) (hr : (r : S) ^ 2 = f d) (x : R) :
    quadraticUnitRingLift f d r h2 hr (algebraMap R (QuadraticEtaleRing d) x) = f x := by
  let : Algebra R S := f.toAlgebra
  exact (quadraticUnitLift d r h2 hr).commutes x

theorem quadraticRingHom_ext (d : Rˣ) (F G : QuadraticEtaleRing d →+* S)
    (hbase : ∀ x, F (algebraMap R (QuadraticEtaleRing d) x) =
      G (algebraMap R (QuadraticEtaleRing d) x))
    (hroot : F (quadraticEtaleUnit d) = G (quadraticEtaleUnit d)) : F = G := by
  let : Algebra R S := (F.comp (algebraMap R (QuadraticEtaleRing d))).toAlgebra
  let a : QuadraticEtaleRing d →ₐ[R] S := { F with commutes' := fun _ => rfl }
  let b : QuadraticEtaleRing d →ₐ[R] S := { G with commutes' := fun x => (hbase x).symm }
  have h : a = b := (quadraticEtalePair d).hom_ext (by
    change F (quadraticEtalePair d).X = G (quadraticEtalePair d).X
    simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using hroot)
  exact congrArg AlgHom.toRingHom h

/-- Lift the parameter swap to the cover while fixing the root of minus one. -/
def legendreSwapRootMap (p : ℕ) :
    LegendreUniversalSwapRing p →+* LegendreUniversalSwapRing p :=
  quadraticUnitRingLift
    ((algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)).comp
      (legendreSwapParameterMap p))
    (-1) (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ))
    ((legendreBase_units p).1.map (algebraMap (LegendreBase p) _))
    (by simpa using quadraticEtaleUnit_square (-1 : (LegendreBase p)ˣ))

theorem legendreSwapRootMap_scalar (p : ℕ) (x : LegendreBase p) :
    legendreSwapRootMap p (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) x) =
      algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) (legendreSwapParameterMap p x) :=
  quadraticUnitRingLift_scalar _ _ _ _ _ x

theorem legendreSwapRootMap_root (p : ℕ) :
    legendreSwapRootMap p (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)) =
      (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ) : LegendreUniversalSwapRing p) :=
  quadraticUnitRingLift_root _ _ _ _ _

theorem legendreSwapRootMap_square (p : ℕ) :
    (legendreSwapRootMap p).comp (legendreSwapRootMap p) = RingHom.id _ := by
  apply quadraticRingHom_ext (-1 : (LegendreBase p)ˣ)
  · intro x
    simp only [RingHom.comp_apply, RingHom.id_apply, legendreSwapRootMap_scalar,
      legendreSwapParameterMap_involutive p x]
  · simp only [RingHom.comp_apply, RingHom.id_apply, legendreSwapRootMap_root]

theorem legendreSwapRootMap_parameter (p : ℕ) :
    legendreSwapRootMap p
      (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) (legendreParameter p)) =
    1 - algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) (legendreParameter p) := by
  rw [legendreSwapRootMap_scalar, legendreSwapParameterMap_parameter, map_sub, map_one]

/-- The actual Legendre equation over the swap root cover. -/
abbrev legendreSwapCoverModel (p : ℕ) : WeierstrassCurve (LegendreUniversalSwapRing p) :=
  (legendreModel p).map (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p))

theorem legendreSwapCover_equation (p : ℕ) :
    legendreSwapChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)) •
      (legendreSwapCoverModel p).map (legendreSwapRootMap p) = legendreSwapCoverModel p := by
  change legendreSwapChange _ •
    ((legendreCurve (legendreParameter p)).map
      (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p))).map _ = _
  rw [legendreCurve_map, legendreCurve_map, legendreSwapRootMap_parameter,
    legendreSwapChange_curve _ _ (legendreSwapRoot_square p)]
  simp [legendreSwapCoverModel, legendreModel, legendreCurve_map]

theorem legendreSwapCover_coordinate_map (p : ℕ) :
    (legendreSwapChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ))).map
      (legendreSwapRootMap p) =
        legendreSwapChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)) := by
  ext <;> simp [legendreSwapChange, VariableChange.map, legendreSwapRootMap_root]

/-- Combine the lifted parameter swap with the swap coordinate transport. -/
def legendreSwapCoverCyclicMap (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel (legendreSwapCoverModel p) p).left ⟶
      (scalarQuotientModel (legendreSwapCoverModel p) p).left :=
  (groupCyclicParameterIso p (variableChangeCongrOverIso
    ((legendreSwapCoverModel p).map (legendreSwapRootMap p)) (legendreSwapCoverModel p)
    (legendreSwapChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)))
    (legendreSwapCover_equation p))).hom.left ≫
      ringHomCyclicMap (legendreSwapCoverModel p) p (legendreSwapRootMap p)

theorem legendreSwapCoverCyclicMap_square (p : ℕ) [Fact p.Prime] :
    legendreSwapCoverCyclicMap p ≫ legendreSwapCoverCyclicMap p = 𝟙 _ := by
  apply cyclicCoordinateRingMap_return_neg (legendreSwapCoverModel p) p
    (legendreSwapRootMap p) (legendreSwapRootMap p) (legendreSwapRootMap_square p)
    (legendreSwapCoverModel p)
    (legendreSwapChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)))
    (legendreSwapChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)))
    (legendreSwapCover_equation p) (legendreSwapCover_equation p)
    (by simp [legendreSwapCoverModel, legendreModel, legendreCurve, WeierstrassCurve.map])
    (by simp [legendreSwapCoverModel, legendreModel, legendreCurve, WeierstrassCurve.map])
  rw [legendreSwapCover_coordinate_map]
  exact legendreSwapChange_mul_self _ (legendreSwapRoot_square p)

/-- The involutive cyclic automorphism over the swap root cover. -/
def legendreSwapCoverCyclicAut (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel (legendreSwapCoverModel p) p).left ≅
      (scalarQuotientModel (legendreSwapCoverModel p) p).left where
  hom := legendreSwapCoverCyclicMap p
  inv := legendreSwapCoverCyclicMap p
  hom_inv_id := legendreSwapCoverCyclicMap_square p
  inv_hom_id := legendreSwapCoverCyclicMap_square p

theorem legendreSwapCoverCyclicMap_toBase (p : ℕ) [Fact p.Prime] :
    legendreSwapCoverCyclicMap p ≫ (scalarQuotientModel (legendreSwapCoverModel p) p).hom =
      (scalarQuotientModel (legendreSwapCoverModel p) p).hom ≫
        Spec.map (CommRingCat.ofHom (legendreSwapRootMap p)) := by
  let e := groupCyclicParameterIso p (variableChangeCongrOverIso
    ((legendreSwapCoverModel p).map (legendreSwapRootMap p)) (legendreSwapCoverModel p)
    (legendreSwapChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)))
    (legendreSwapCover_equation p))
  change (e.hom.left ≫ ringHomCyclicMap _ p _) ≫ _ = _
  rw [Category.assoc, ringHomCyclicMap_toBase, ← Category.assoc]
  exact congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom (legendreSwapRootMap p))) e.hom.w
end WeierstrassCurve.CubicCharts
