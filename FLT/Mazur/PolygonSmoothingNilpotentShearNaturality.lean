/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentShear
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# Quotient naturality of full nilpotent node shears

Arbitrary coefficient maps preserve both the full chart correction and its
smoothing drift. The same square holds for the constructed inverses; no
compatible choices of finite contraction inverses are required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) (hs : f t = s) (e : R) (he : IsNilpotent e)
local notation "F" => ringMap f t s hs

/-- The full chart unit commutes with the specified coefficient map. -/
theorem nilpotentChartMultiplier_map (p : ChartRing t) :
    Units.map F (nilpotentChartMultiplier t e he p) =
      nilpotentChartMultiplier s (f e) (he.map f) (F p) := by
  apply Units.ext
  change F (nilpotentChartMultiplier t e he p : ChartRing t) = _
  rw [nilpotentChartMultiplier_val, nilpotentChartMultiplier_val,
    RingHom.map_add,
    map_one (F), map_mul (F), ringMap_scalar]

/-- The inverse unit also changes coefficients without choosing a new inverse. -/
theorem nilpotentChartMultiplier_map_inv (p : ChartRing t) :
    F (↑(nilpotentChartMultiplier t e he p)⁻¹ : ChartRing t) =
      (↑(nilpotentChartMultiplier s (f e) (he.map f) (F p))⁻¹ : ChartRing s) := by
  have h := congrArg (fun v : (ChartRing s)ˣ ↦ (↑v⁻¹ : ChartRing s))
    (nilpotentChartMultiplier_map f t s hs e he p)
  rw [← map_inv] at h
  exact h

include hs in
/-- Changing coefficients transports the smoothing drift exactly. -/
theorem nilpotentShear_parameter_map (c : R) :
    f ((1 + e * c) * t) = (1 + f e * f c) * s := by
  rw [map_mul, map_add, map_one, map_mul, hs]

/-- The whole forward node map is natural under arbitrary coefficient changes. -/
theorem nilpotentShearEquiv_naturality (c : R) (p : ChartRing t) :
    (F).comp (nilpotentShearEquiv t e he c p).toAlgHom.toRingHom =
      (nilpotentShearEquiv s (f e) (he.map f) (f c) (F p)).toAlgHom.toRingHom.comp
        (ringMap f ((1 + e * c) * t) ((1 + f e * f c) * s)
          (nilpotentShear_parameter_map f t s hs e c)) := by
  apply chartRing_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom,
      AlgEquiv.commutes, ringMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom,
      nilpotentShearEquiv_left, map_mul (F),
      RingHom.map_add, map_one (F),
      ringMap_left, ringMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom,
      nilpotentShearEquiv_right, map_mul, ringMap_scalar, ringMap_right,
      nilpotentChartMultiplier_map_inv, f.map_add, f.map_one]

/-- Naturality of the full inverse follows from the forward square and injectivity. -/
theorem nilpotentShearEquiv_symm_naturality (c : R) (p : ChartRing t) :
    (ringMap f ((1 + e * c) * t) ((1 + f e * f c) * s)
        (nilpotentShear_parameter_map f t s hs e c)).comp
      (nilpotentShearEquiv t e he c p).symm.toAlgHom.toRingHom =
      (nilpotentShearEquiv s (f e) (he.map f) (f c) (F p)).symm.toAlgHom.toRingHom.comp F := by
  apply RingHom.ext
  intro z
  apply (nilpotentShearEquiv s (f e) (he.map f) (f c) (F p)).injective
  have h := DFunLike.congr_fun (nilpotentShearEquiv_naturality f t s hs e he c p)
    ((nilpotentShearEquiv t e he c p).symm z)
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply] using h.symm

end FLT.Mazur.PolygonSmoothing
