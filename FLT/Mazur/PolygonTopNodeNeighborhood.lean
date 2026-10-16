/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeAutomorphism
public import FLT.Mazur.PolygonSmoothingCoordinateIdeal

/-!
# Top-layer coordinate changes retain every original node neighborhood

The full original coordinate ideal, rather than its radical, is invariant
under an endomorphism trivial at the preceding smoothing stage. Its powers
therefore carry compatible quotient automorphisms induced by the unchanged
node map. No reduced replacement of the node or coefficient ring occurs.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "I" => coordinateIdeal (e)
variable (f : ChartRing (parameter R (m + 1)) →ₐ[Ring R (m + 1)]
  ChartRing (parameter R (m + 1)))
  (hf : ∀ z, topNodeRestriction R m (f z) = topNodeRestriction R m z)

include hf

/-- Every exact coordinate difference lies in the original joint node ideal. -/
theorem topNodeEndomorphism_difference_mem (z : B) : f z - z ∈ (I) := by
  have he := (Algebra.smul_def ((e) ^ (m + 1))
    (topNodeDifference R m f hf z)).symm.trans (topNodeDifference_spec R m f hf z)
  rw [← he, map_pow]
  exact (I).mul_mem_right _
    ((I).pow_mem_of_mem (parameter_mem_coordinateIdeal (e)) (m + 1) (by omega))

/-- Original node-ideal membership is equivalent before and after the full coordinate change. -/
theorem topNodeEndomorphism_mem_coordinateIdeal (z : B) : f z ∈ (I) ↔ z ∈ (I) := by
  have hd := topNodeEndomorphism_difference_mem R m f hf z
  constructor
  · intro hz
    have he : z = f z - (f z - z) := by abel
    rw [he]
    exact (I).sub_mem hz hd
  · intro hz
    simpa only [sub_add_cancel] using (I).add_mem hd hz

/-- Pullback retains the entire original coordinate ideal. -/
theorem topNodeEndomorphism_coordinateIdeal_comap : (I).comap f.toRingHom = (I) := by
  ext z
  exact topNodeEndomorphism_mem_coordinateIdeal R m f hf z

/-- Pushforward also retains that same ideal, using the constructed genuine inverse. -/
theorem topNodeEndomorphism_coordinateIdeal_map : (I).map f.toRingHom = (I) := by
  have he := Ideal.map_comap_of_surjective f.toRingHom
    (topNodeEndomorphismEquiv R m f hf).surjective (I)
  rw [topNodeEndomorphism_coordinateIdeal_comap R m f hf] at he
  exact he

/-- Every full power of the node ideal is preserved exactly. -/
theorem topNodeEndomorphism_coordinateIdeal_pow (k : ℕ) :
    ((I) ^ k).map f.toRingHom = (I) ^ k := by
  rw [Ideal.map_pow, topNodeEndomorphism_coordinateIdeal_map R m f hf]

/-- The original coordinate change on each full node neighborhood. -/
def topNodeNeighborhoodEquiv (k : ℕ) : ((B) ⧸ (I) ^ k) ≃ₐ[S] ((B) ⧸ (I) ^ k) :=
  Ideal.quotientEquivAlg _ _ (topNodeEndomorphismEquiv R m f hf)
    (topNodeEndomorphism_coordinateIdeal_pow R m f hf k).symm

/-- Quotient coordinates are obtained from the original map on representatives. -/
theorem topNodeNeighborhoodEquiv_mk (k : ℕ) (z : B) :
    topNodeNeighborhoodEquiv R m f hf k (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (f z) := Ideal.quotientEquivAlg_mk ..

/-- Every quotient automorphism commutes with the original node-neighborhood transition. -/
theorem topNodeNeighborhoodEquiv_transition {k l : ℕ} (hkl : k ≤ l)
    (z : (B) ⧸ (I) ^ l) :
    Ideal.Quotient.factorₐ (S) (Ideal.pow_le_pow_right hkl)
        (topNodeNeighborhoodEquiv R m f hf l z) =
      topNodeNeighborhoodEquiv R m f hf k
        (Ideal.Quotient.factorₐ (S) (Ideal.pow_le_pow_right hkl) z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [topNodeNeighborhoodEquiv_mk, Ideal.Quotient.factorₐ_apply_mk]

end FLT.Mazur.PolygonInfinitesimalStages
