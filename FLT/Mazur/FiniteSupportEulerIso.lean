/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSupportEulerPositive

/-!
# Equal Euler characteristics eliminate a finite-support comparison error

An injective coherent comparison on a proper scheme is an isomorphism when
its cokernel has finite support and the two Euler characteristics agree.
This applies to the structure inclusion of a finite birational curve map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
open CoherentDevissage
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation]
  (a : M ⟶ N) [Mono a]

/-- A finite-support coherent error with zero Euler characteristic vanishes. -/
theorem cokernel_isZero_of_euler_eq (ha : (support (cokernel a)).Finite)
    (he : curveEulerCharacteristic f M = curveEulerCharacteristic f N) :
    IsZero (cokernel a) := by
  let _ := Chow.source_isNoetherian f
  let _ := coherent_cokernel a
  have hadd := curveEulerCharacteristic_add_finiteSupport f
    (ShortComplex.cokernelSequence a) (coherent_cokernelSequence a) ha
  change curveEulerCharacteristic f N =
    curveEulerCharacteristic f M + curveEulerCharacteristic f (cokernel a) at hadd
  by_contra hne
  have hpos := finiteSupport_euler_pos f (cokernel a) ha hne
  omega

/-- An injective coherent comparison with finite error and equal Euler characteristics is an iso. -/
theorem isIso_of_finiteSupport_euler_eq (ha : (support (cokernel a)).Finite)
    (he : curveEulerCharacteristic f M = curveEulerCharacteristic f N) : IsIso a := by
  have hz := cokernel_isZero_of_euler_eq f a ha he
  let _ : Epi a := Abelian.epi_of_cokernel_π_eq_zero a (hz.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi a

end FLT.Mazur.FCurve
