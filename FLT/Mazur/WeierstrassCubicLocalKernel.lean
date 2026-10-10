/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicQuotientChart
public import FLT.Mazur.WeierstrassCubicMultiplication

/-!
# The local kernel of the genuine cubic sequence

The original chart algebra identifies the kernel ideal on standard opens.
Quasi-coherence restricts this equality to every affine subopen. The actual
O(-3) trivialization realizes each element of that ideal as a multiple of the cubic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open FLT.Mazur.ProjectiveSpace FLT.Mazur.FCurve
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- A standard projective open with its proved affine structure. -/
def cubicAmbientAffineChart (j : Fin 3) : (space R (Fin 3)).affineOpens :=
  ⟨chart R (Fin 3) j,
    Proj.isAffineOpen_basicOpen _ _ (isHomogeneous_X R j) (by decide)⟩

/-- The kernel on actual ambient chart sections is precisely the principal cubic ideal. -/
theorem cubicQuotient_chart_kernel (j : Fin 3) :
    RingHom.ker ((integralProjectiveMap W).app (chart R (Fin 3) j)).hom =
      Ideal.span {cubicEquationSection W j} := by
  let e := Proj.basicOpenIsoAway (grading R (Fin 3)) (X j)
    (isHomogeneous_X R j) (by decide)
  ext s
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).surjective s
  change (integralProjectiveMap W).app (chart R (Fin 3) j)
    (Proj.awayToSection _ _ a) = 0 ↔ _
  rw [cubicQuotient_chart_mem_iff]
  change a ∈ Ideal.span {projectiveChartEquation W j} ↔
    e.hom a ∈ Ideal.span {e.hom (projectiveChartEquation W j)}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact (map_dvd_iff e.commRingCatIsoToRingEquiv).symm

/-- The same principal kernel description holds on every affine subopen of a chart. -/
theorem cubicQuotient_affine_kernel (j : Fin 3) (V : (space R (Fin 3)).affineOpens)
    (h : V.1 ≤ chart R (Fin 3) j) :
    RingHom.ker ((integralProjectiveMap W).app V.1).hom =
      Ideal.span {res h (cubicEquationSection W j)} := by
  have he := (integralProjectiveMap W).ker.map_ideal
    (show V ≤ cubicAmbientAffineChart (R := R) j from h)
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at he
  change Ideal.map (res h)
    (RingHom.ker ((integralProjectiveMap W).app (chart R (Fin 3) j)).hom) = _ at he
  rw [cubicQuotient_chart_kernel, Ideal.map_span, Set.image_singleton] at he
  exact he.symm

/-- On a subopen of one chart, the original multiplication is the expected scalar product. -/
theorem cubicStructureMultiply_onChart (j : Fin 3) {V : (space R (Fin 3)).Opens}
    (h : V ≤ chart R (Fin 3) j) (s : (twistCocycle R (Fin 3) (-3)).sections V) :
    (cubicStructureMultiply W).app V s =
      (twistCocycle R (Fin 3) (-3)).evaluate j h s * res h (cubicEquationSection W j) := by
  have he := congrArg (res (le_inf le_rfl h)) (cubicStructureMultiply_coordinate W V s j)
  simpa only [map_mul, res_res, res_self, Cocycle.evaluate] using he

/-- Every local multiple has a preimage in the actual negative twisting sheaf. -/
theorem cubicStructureMultiply_extend (j : Fin 3) {V : (space R (Fin 3)).Opens}
    (h : V ≤ chart R (Fin 3) j) (a : Γ(space R (Fin 3), V)) :
    (cubicStructureMultiply W).app V ((twistCocycle R (Fin 3) (-3)).extend j h a) =
      a * res h (cubicEquationSection W j) := by
  rw [cubicStructureMultiply_onChart, Cocycle.evaluate_extend]

/-- Kernel sections lift through cubic multiplication on every affine chart subopen. -/
theorem cubicQuotient_affine_lift (j : Fin 3) (V : (space R (Fin 3)).affineOpens)
    (h : V.1 ≤ chart R (Fin 3) j) (s : Γ(space R (Fin 3), V.1))
    (hs : (cubicStructureQuotient W).app V.1 s = 0) :
    ∃ t, (cubicStructureMultiply W).app V.1 t = s := by
  have hm : s ∈ RingHom.ker ((integralProjectiveMap W).app V.1).hom := hs
  rw [cubicQuotient_affine_kernel W j V h, Ideal.mem_span_singleton'] at hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨(twistCocycle R (Fin 3) (-3)).extend j h a,
    (cubicStructureMultiply_extend W j h a).trans ha⟩

end FLT.Mazur.WeierstrassIntegralChart
