/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphFlat
public import FLT.Mazur.PolygonStageCoefficientChange

/-!
# Descent from flatness over the unchanged smaller stage base

A coefficient map into the node coefficients retains the actual smoothing
parameter and all of its powers. Flatness of the finite graph over this
original smaller base therefore suffices for descent at every top layer.
The geometric flatness premise is explicit and is not asserted here.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonChartScaling PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal topNodeActionDefect
  topNodeGraphAlgebra
variable (R : Type) [CommRing R] (m : ℕ)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ) (a : (Ring R (m + 1))ˣ)
variable {A : Type} [CommRing A] (f : A →+* R)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "C" => stageNodeBranchSubalgebra R (m + 1)
local notation "β" => stageNodeBranchPair R (m + 1)
local notation "F" => stageNodeBranchSubstitution R (m + 1) u v
local notation "D" => topNodeActionDefect R m u v a
local notation "G" => topNodeGraphAlgebra R m u v
local notation "σ" => reciprocalScale (e) a

/-- The original stage coefficient map into the full source-target graph. -/
def topNodeGraphOriginalScalars : Ring A (m + 1) →+* (G) :=
  (algebraMap (S) (G)).comp (stageCoefficientMap f (m + 1))

/-- This smaller base map keeps the actual smoothing parameter. -/
theorem topNodeGraphOriginalScalars_parameter :
    topNodeGraphOriginalScalars R m u v f (parameter A (m + 1)) =
      algebraMap (S) (G) (e) := by
  change algebraMap (S) (G) (stageCoefficientMap f (m + 1) (parameter A (m + 1))) = _
  rw [stageCoefficientMap_parameter]

variable
  (hu : coeffMap (restriction R m).toRingHom u.val =
    LaurentPolynomial.C (restriction R m a.val) * T 1)
  (hv : coeffMap (restriction R m).toRingHom v.val =
    LaurentPolynomial.C (restriction R m a⁻¹.val) * T 1)
include hu hv

/-- Original smaller-base flatness forces every full defect into the original node. -/
theorem topNodeGraphOriginalFlat_defect
    (hf : (topNodeGraphOriginalScalars R m u v f).Flat) (z : B) : (D) z ∈ (C) := by
  let _ := (topNodeGraphOriginalScalars R m u v f).toAlgebra
  let _ : Module.Flat (Ring A (m + 1)) (G) := hf
  have hs (k : ℕ) (w : G) :
      ((parameter A (m + 1) ^ k) • w).val = (e) ^ k • w.val := by
    change algebraMap (S) ((S)[T;T⁻¹] × (S)[T;T⁻¹])
      (stageCoefficientMap f (m + 1) (parameter A (m + 1) ^ k)) * w.val = _
    rw [map_pow, stageCoefficientMap_parameter, Algebra.smul_def]
  let d : G := ⟨(D) z, topNodeGraphAlgebra_defect R m u v a z⟩
  have hd : parameter A (m + 1) • d = 0 := by
    apply Subtype.ext
    have he := hs 1 d
    simp only [pow_one] at he
    rw [he]
    exact topNodeActionDefect_parameter R m u v a hu hv z
  obtain ⟨w, hw⟩ := (flat_parameter_smul_eq_zero_iff A m (G) d).mp hd
  have he : (e) ^ (m + 1) • w.val = (D) z := by
    have hh := congrArg Subtype.val hw
    change ((parameter A (m + 1) ^ (m + 1)) • w).val = (D) z at hh
    rw [hs] at hh
    exact hh
  rw [← he]
  exact topNodeGraphAlgebra_topParameter R m u v a hu hv w.val w.property

/-- Original smaller-base flatness preserves all original node functions. -/
theorem topNodeGraphOriginalFlat_preserves
    (hf : (topNodeGraphOriginalScalars R m u v f).Flat)
    (p : (S)[T;T⁻¹] × (S)[T;T⁻¹]) (hp : p ∈ (C)) : (F) p ∈ (C) := by
  obtain ⟨z, hz⟩ := hp
  change (β) z = p at hz
  rw [← hz]
  have hd := topNodeGraphOriginalFlat_defect R m u v a f hu hv hf z
  have hs : (β) ((σ) z) ∈ (C) := ⟨_, rfl⟩
  simpa only [topNodeActionDefect_apply, sub_add_cancel] using (C).add_mem hd hs

/-- Flatness over the unchanged smaller base implies flatness over the full coefficients. -/
theorem topNodeGraphOriginalFlat_coefficients
    (hf : (topNodeGraphOriginalScalars R m u v f).Flat) : Module.Flat (S) (G) :=
  (topNodeGraphFlat_iff_preserves R m u v a hu hv).mpr
    (topNodeGraphOriginalFlat_preserves R m u v a f hu hv hf)

end FLT.Mazur.PolygonInfinitesimalStages
