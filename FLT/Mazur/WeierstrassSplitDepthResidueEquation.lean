/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueFiber
public import FLT.Mazur.WeierstrassSplitNodalLaurent

/-!
# The original cubic at positive split depth

The actual coefficient reduction is the split nodal equation, with its
original ordered tangent coefficient. Equality transports every normalized
chart and every original coordinate, including the chart at infinity.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
open WeierstrassDilatation

include hdepth in
/-- Positive depth reduces the original equation to the split nodal cubic. -/
theorem splitDepth_residue_equation :
    W.map (algebraMap R (ResidueField R)) = splitNodalEquation (residueTangentUnit D) := by
  have h3 : W.a₃ = π ^ 0 * W.a₃ := by simp
  have h4 : W.a₄ = π ^ 0 * W.a₄ := by simp
  have h6 : W.a₆ = (π ^ 0) ^ 2 * W.a₆ := by simp
  obtain ⟨hb3, hb4⟩ := divided_linear_mem D 0 (by omega) W.a₃ W.a₄ h3 h4
  have hb6 := divided_constant_mem D 0 (by omega) W.a₆ h6
  ext
  · exact (residueTangentUnit_val D).symm
  · exact (residue_eq_zero_iff _).mpr D.a₂_mem
  · exact (residue_eq_zero_iff _).mpr hb3
  · exact (residue_eq_zero_iff _).mpr hb4
  · exact (residue_eq_zero_iff _).mpr hb6

variable {S : Type*} [CommRing S] {U V : WeierstrassCurve S}

/-- Equality of equations retains the whole coordinate algebra of every chart. -/
def equationChartEquiv (h : U = V) (j : Fin 3) : Coordinate U j ≃ₐ[S] Coordinate V j :=
  h ▸ AlgEquiv.refl

/-- Equation transport fixes the original normalized projective coordinates. -/
theorem equationChartEquiv_coord (h : U = V) (j i : Fin 3) :
    equationChartEquiv h j (coord U j i) = coord V j i := by
  subst V
  rfl

end FLT.Mazur.WeierstrassIntegralChart
