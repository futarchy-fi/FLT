/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantSmoothPresentation
public import FLT.Mazur.WeierstrassSplitDepthAffineParameters

/-!
# The genuine smooth affine/Y parameter lies in the secant refinement

The residue cubic equation and the actual Y-chart overlap force the first
abscissa to be a unit. No invertibility premise on the smooth abscissa is
needed to factor the nodal residue input through the ordinary secant chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] {W : WeierstrassCurve R} {π : R} {depth : ℕ}
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
  (a c : Coordinate W 2 →ₐ[R] S) (v : Coordinate W 1 →ₐ[R] S)
  (hv : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 =
    Spec.map (CommRingCat.ofHom v.toRingHom) ≫ integralCurveChart W 1)
  {C : Type*} [CommRing C] (e : S →+* C)
  (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker e)

include D hdepth hv hJ in
/-- The actual affine/Y overlap forces the smooth abscissa to be a residue unit. -/
theorem splitDepthSmooth_abscissa_unit : IsUnit (e (a (coord W 2 0))) := by
  have cross (i : Fin 3) : e (a (coord W 2 i)) =
      e (a (coord W 2 1)) * e (v (coord W 1 i)) := by
    rw [(chart_algHom_global_eq_iff W 2 1 a v).mp hv i, map_mul]
  obtain ⟨r, q, _, hx, _, _⟩ := splitDepthAffine_exists_normalized_units
    D hdepth a e hJ (fun i => e (v (coord W 1 i))) cross
  rw [hx]
  exact r.isUnit.mul q.isUnit

variable (hc : e (c (coord W 2 0)) = 0)

/-- The actual smooth by node residue map into the concrete ordinary refinement. -/
def splitDepthSecantResidue : SecantPairRing W a c →+* C :=
  secantPairResidue W a c e (splitDepthSmooth_abscissa_unit D hdepth a v hv e hJ) hc

/-- The constructed factorization contracts to the entire original residue map. -/
@[simp] theorem splitDepthSecantResidue_base (s : S) :
    splitDepthSecantResidue D hdepth a c v hv e hJ hc
      (algebraMap S (SecantPairRing W a c) s) = e s :=
  secantPairResidue_base ..

/-- The ordinary left coordinates are those of the actual original smooth point. -/
@[simp] theorem splitDepthSecantResidue_left (t : Coordinate W 2) :
    splitDepthSecantResidue D hdepth a c v hv e hJ hc
      (secantPairPresentation W a c (ordinaryInputLeft W false t)) = e (a t) :=
  secantPairResidue_left ..

/-- The ordinary right coordinates are those of the actual original node. -/
@[simp] theorem splitDepthSecantResidue_right (t : Coordinate W 2) :
    splitDepthSecantResidue D hdepth a c v hv e hJ hc
      (secantPairPresentation W a c (ordinaryInputRight W false t)) = e (c t) :=
  secantPairResidue_right ..

end FLT.Mazur.WeierstrassIntegralChart
