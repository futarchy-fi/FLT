/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreSwapLift
public import FLT.EllipticCurve.CubicLegendreReciprocalRefinement
/-! # The global cyclic reciprocal is an involution

Parameter inversion lifts to the quadratic parameter-root cover by sending
the distinguished root to its inverse. Combining it with the return coordinate
scaling gives a local cyclic involution. The actual descended return
factorization identifies this with the global reciprocal automorphism,
whose square is therefore identity after canceling the covering projection.

The mixed global relation and the modular quotient remain to be constructed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts

theorem legendreReciprocalRoot_inv_square (p : ℕ) :
    (((quadraticEtaleUnit (legendreParameterUnit p))⁻¹ :
      (LegendreUniversalReciprocalRing p)ˣ) : LegendreUniversalReciprocalRing p) ^ 2 =
      algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)
        (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) := by
  have h : (quadraticEtaleUnit (legendreParameterUnit p)) ^ 2 =
      Units.map (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)).toMonoidHom
        (legendreParameterUnit p) := by
    ext
    exact quadraticEtaleUnit_square (legendreParameterUnit p)
  change (((quadraticEtaleUnit (legendreParameterUnit p))⁻¹ ^ 2 :
    (LegendreUniversalReciprocalRing p)ˣ) : LegendreUniversalReciprocalRing p) = _
  rw [inv_pow, h, ← map_inv]
  rfl

/-- Lift parameter inversion by inverting the distinguished quadratic root. -/
def legendreReciprocalRootMap (p : ℕ) :
    LegendreUniversalReciprocalRing p →+* LegendreUniversalReciprocalRing p :=
  quadraticUnitRingLift
    ((algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)).comp
      (legendreReciprocalParameterMap p))
    (legendreParameterUnit p) (quadraticEtaleUnit (legendreParameterUnit p))⁻¹
    (legendreReciprocalRoot_units p).1
    (by simpa only [RingHom.comp_apply, legendreParameterUnit_val,
      legendreReciprocalParameterMap_parameter] using legendreReciprocalRoot_inv_square p)

theorem legendreReciprocalRootMap_scalar (p : ℕ) (x : LegendreBase p) :
    legendreReciprocalRootMap p
      (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p) x) =
    algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)
      (legendreReciprocalParameterMap p x) :=
  quadraticUnitRingLift_scalar _ _ _ _ _ x

theorem legendreReciprocalRootMap_root (p : ℕ) :
    legendreReciprocalRootMap p (quadraticEtaleUnit (legendreParameterUnit p)) =
      (((quadraticEtaleUnit (legendreParameterUnit p))⁻¹ :
        (LegendreUniversalReciprocalRing p)ˣ) : LegendreUniversalReciprocalRing p) :=
  quadraticUnitRingLift_root _ _ _ _ _

theorem legendreReciprocalRootMap_root_unit (p : ℕ) :
    Units.map (legendreReciprocalRootMap p).toMonoidHom
      (quadraticEtaleUnit (legendreParameterUnit p)) =
        (quadraticEtaleUnit (legendreParameterUnit p))⁻¹ := by
  ext
  exact legendreReciprocalRootMap_root p

theorem legendreReciprocalRootMap_root_inv (p : ℕ) :
    legendreReciprocalRootMap p
      (((quadraticEtaleUnit (legendreParameterUnit p))⁻¹ :
        (LegendreUniversalReciprocalRing p)ˣ) : LegendreUniversalReciprocalRing p) =
      (quadraticEtaleUnit (legendreParameterUnit p) : LegendreUniversalReciprocalRing p) := by
  change ((Units.map (legendreReciprocalRootMap p).toMonoidHom
    ((quadraticEtaleUnit (legendreParameterUnit p))⁻¹)) : LegendreUniversalReciprocalRing p) = _
  rw [map_inv, legendreReciprocalRootMap_root_unit, inv_inv]

theorem legendreReciprocalRootMap_square (p : ℕ) :
    (legendreReciprocalRootMap p).comp (legendreReciprocalRootMap p) = RingHom.id _ := by
  apply quadraticRingHom_ext (legendreParameterUnit p)
  · intro x
    simp only [RingHom.comp_apply, RingHom.id_apply, legendreReciprocalRootMap_scalar,
      legendreReciprocalParameterMap_involutive p x]
  · simp only [RingHom.comp_apply, RingHom.id_apply, legendreReciprocalRootMap_root,
      legendreReciprocalRootMap_root_inv]

theorem legendreReciprocalRootMap_parameter (p : ℕ) :
    legendreReciprocalRootMap p
      (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p) (legendreParameter p)) =
    ((legendreReciprocalLiftedParameter p)⁻¹ : (LegendreUniversalReciprocalRing p)ˣ) := by
  rw [legendreReciprocalRootMap_scalar, legendreReciprocalParameterMap_parameter]
  rfl

/-- The Legendre model over its universal parameter-root cover. -/
abbrev legendreReciprocalCoverModel (p : ℕ) :
    WeierstrassCurve (LegendreUniversalReciprocalRing p) :=
  (legendreModel p).map (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p))

theorem legendreReciprocalCover_equation (p : ℕ) :
    legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p))⁻¹ •
      (legendreReciprocalCoverModel p).map (legendreReciprocalRootMap p) =
        legendreReciprocalCoverModel p := by
  change legendreReciprocalChange _ •
    ((legendreCurve (legendreParameter p)).map
      (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p))).map _ = _
  rw [legendreCurve_map, legendreCurve_map, legendreReciprocalRootMap_parameter,
    legendreReciprocalChange_curve _ _ (legendreReciprocalRoot_inv_square p), inv_inv]
  simp [legendreReciprocalCoverModel, legendreModel, legendreCurve_map,
    legendreReciprocalLiftedParameter]


theorem legendreReciprocalCover_coordinate_map (p : ℕ) :
    (legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p))⁻¹).map
      (legendreReciprocalRootMap p) =
        legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p)) := by
  ext <;> simp [legendreReciprocalChange, VariableChange.map,
    legendreReciprocalRootMap_root_inv]

/-- The semilinear reciprocal return on cyclic parameters over the root cover. -/
def legendreReciprocalCoverCyclicMap (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel (legendreReciprocalCoverModel p) p).left ⟶
      (scalarQuotientModel (legendreReciprocalCoverModel p) p).left :=
  (groupCyclicParameterIso p (variableChangeCongrOverIso
    ((legendreReciprocalCoverModel p).map (legendreReciprocalRootMap p))
    (legendreReciprocalCoverModel p)
    (legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p))⁻¹)
    (legendreReciprocalCover_equation p))).hom.left ≫
      ringHomCyclicMap (legendreReciprocalCoverModel p) p (legendreReciprocalRootMap p)

theorem legendreReciprocalCoverCyclicMap_square (p : ℕ) [Fact p.Prime] :
    legendreReciprocalCoverCyclicMap p ≫ legendreReciprocalCoverCyclicMap p = 𝟙 _ := by
  apply cyclicCoordinateRingMap_return_one (legendreReciprocalCoverModel p) p
    (legendreReciprocalRootMap p) (legendreReciprocalRootMap p)
    (legendreReciprocalRootMap_square p) (legendreReciprocalCoverModel p)
    (legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p))⁻¹)
    (legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p))⁻¹)
    (legendreReciprocalCover_equation p) (legendreReciprocalCover_equation p)
  rw [legendreReciprocalCover_coordinate_map]
  exact legendreReciprocalChange_inv_mul _

theorem legendreReciprocalDescendedIso_inv (p : ℕ) [Fact p.Prime] :
    (legendreReciprocalDescendedIso p).inv.left =
      legendreReciprocalReturnDescendedMap p :=
  (congrArg Over.Hom.left (legendreReciprocalReturnDescendedOver_eq_inv p)).symm

theorem legendreReciprocalCyclicAut_hom (p : ℕ) [Fact p.Prime] :
    (legendreReciprocalCyclicAut p).hom =
      legendreReciprocalReturnDescendedMap p ≫
        (cyclicModelCongr _ p _ (legendreReciprocal_model_map p)).inv.left ≫
          ringHomCyclicMap (legendreModel p) p
            (legendreReciprocalParameterEquiv p).toRingHom := by
  change ((legendreReciprocalDescendedIso p).inv.left ≫
    (cyclicModelCongr _ p _ (legendreReciprocal_model_map p)).inv.left) ≫
      (ringEquivCyclicIso _ p _).hom = _
  rw [legendreReciprocalDescendedIso_inv, ringEquivCyclicIso_ringHom, Category.assoc]

theorem legendreReciprocalRootMap_base (p : ℕ) :
    (legendreReciprocalRootMap p).comp
        (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) =
      (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)).comp
        (legendreReciprocalParameterEquiv p).toRingHom := by
  ext x
  exact legendreReciprocalRootMap_scalar p x

attribute [local irreducible] variableChangeCongrOverIso groupCyclicParameterIso

theorem legendreReciprocalCoverCyclicMap_comparison (p : ℕ) [Fact p.Prime] :
    legendreReciprocalCoverCyclicMap p ≫
        ringHomCyclicMap (legendreModel p) p
          (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) =
      ringHomCyclicMap (legendreModel p) p
          (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) ≫
        (legendreReciprocalCyclicAut p).hom := by
  rw [legendreReciprocalCyclicAut_hom,
    ← Category.assoc _ (legendreReciprocalReturnDescendedMap p),
    legendreReciprocalReturn_original_fac, cyclicModelCongr_inv]
  simp only [Category.assoc]
  rw [← Category.assoc (ringHomCyclicMap
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p
      (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p))),
    ringHomCyclicMap_curve_congr]
  simp only [← Category.assoc]
  rw [variableChangeCyclic_source_congr]
  simp only [Category.assoc]
  rw [ringHomCyclicMap_comp, ← Category.assoc, variableChangeCyclic_source_congr]
  unfold legendreReciprocalCoverCyclicMap
  rw [Category.assoc, ringHomCyclicMap_comp_eq _ _
    (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p))
    (legendreReciprocalRootMap p)
    ((algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)).comp
      (legendreReciprocalParameterEquiv p).toRingHom)
    (legendreReciprocalRootMap_base p),
    ← Category.assoc, variableChangeCyclic_source_congr]

theorem legendreReciprocalCyclicAut_square (p : ℕ) [Fact p.Prime] :
    (legendreReciprocalCyclicAut p).hom ≫ (legendreReciprocalCyclicAut p).hom = 𝟙 _ := by
  let q := ringHomCyclicMap (legendreModel p) p
    (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p))
  have : Epi q := by
    dsimp [q]
    rw [ringHomCyclicMap_algebraMap]
    infer_instance
  apply (cancel_epi q).mp
  dsimp [q]
  rw [← Category.assoc, ← legendreReciprocalCoverCyclicMap_comparison, Category.assoc,
    ← legendreReciprocalCoverCyclicMap_comparison, ← Category.assoc,
    legendreReciprocalCoverCyclicMap_square, Category.id_comp, Category.comp_id]

end WeierstrassCurve.CubicCharts
