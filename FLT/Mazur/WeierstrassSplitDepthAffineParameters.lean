/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthConormal
public import FLT.Mazur.WeierstrassSplitNodalAffineParameters

/-!
# Smooth affine parameters from the original integral cubic

After any restriction killing the base maximal ideal, the actual integral
coordinates obey the nodal equation. On the smooth Y overlap this constructs
both unit parameters, rather than assuming the two coordinate formulas.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open IsLocalRing WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S C : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [CommRing C]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ}
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
  (f : Coordinate W 2 →ₐ[R] S) (e : S →+* C)
  (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker e)

include D hdepth hJ in
/-- The original affine coordinates satisfy the nodal equation after base residue restriction. -/
theorem splitDepthAffine_residue_equation :
    e (f (coord W 2 1)) ^ 2 + e (algebraMap R S W.a₁) *
      e (f (coord W 2 0)) * e (f (coord W 2 1)) = e (f (coord W 2 0)) ^ 3 := by
  have kill (r : R) (hr : r ∈ maximalIdeal R) : e (algebraMap R S r) = 0 :=
    hJ (Ideal.mem_map_of_mem _ hr)
  obtain ⟨h3, h4⟩ := divided_linear_mem D 0 (by omega) W.a₃ W.a₄ (by simp) (by simp)
  have h6 := divided_constant_mem D 0 (by omega) W.a₆ (by simp)
  have h := affine_equation_of_hom W f
  rw [WeierstrassCurve.Affine.equation_iff] at h
  have he := congrArg e h
  simpa only [WeierstrassCurve.map, WeierstrassCurve.toAffine, map_add, map_mul,
    map_pow, kill W.a₂ D.a₂_mem, kill W.a₃ h3, kill W.a₄ h4, kill W.a₆ h6,
    zero_mul, add_zero] using he

include D hdepth hJ in
/-- The genuine integral smooth affine input supplies both units and both coordinate identities. -/
theorem splitDepthAffine_exists_units (hy : IsUnit (e (f (coord W 2 1)))) :
    ∃ r q : Cˣ, (q : C) = (r : C) + e (algebraMap R S W.a₁) ∧
      e (f (coord W 2 0)) = (r : C) * q ∧
      e (f (coord W 2 1)) = (r : C) ^ 2 * q := by
  obtain ⟨r, hq, hx, hyr⟩ := splitNodalAffine_exists_parameter
    (splitDepthAffine_residue_equation D hdepth f e hJ) hy
  exact ⟨r, hq.unit, hq.unit_spec, by simpa only [hq.unit_spec] using hx,
    by simpa only [hq.unit_spec] using hyr⟩

include D hdepth hJ in
/-- On a common affine and normalized Y chart, the original normalized X is the inverse slope. -/
theorem splitDepthAffine_exists_normalized_units (v : Fin 3 → C)
    (hv : ∀ i, e (f (coord W 2 i)) = e (f (coord W 2 1)) * v i) :
    ∃ r q : Cˣ, (q : C) = (r : C) + e (algebraMap R S W.a₁) ∧
      e (f (coord W 2 0)) = (r : C) * q ∧
      e (f (coord W 2 1)) = (r : C) ^ 2 * q ∧ v 0 = (↑r⁻¹ : C) := by
  have h2 := hv 2
  rw [coord_self, map_one, map_one] at h2
  have hy := isUnit_of_mul_isUnit_left (h2 ▸ isUnit_one)
  obtain ⟨r, q, hq, hx, hyr⟩ := splitDepthAffine_exists_units D hdepth f e hJ hy
  refine ⟨r, q, hq, hx, hyr, ?_⟩
  apply (r.isUnit.pow 2 |>.mul q.isUnit).mul_left_inj.mp
  have h0 := hv 0
  rw [hx, hyr] at h0
  linear_combination -h0 - (r : C) * q * (Units.mul_inv r)

end FLT.Mazur.WeierstrassIntegralChart
