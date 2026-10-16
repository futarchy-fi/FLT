/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeForwardCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXReflectionCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXOppositeNodeGeometry

/-!
# The complete opposite initial node chart commutes with coefficient change

The full original reflection and initial evaluation give the opposite-label
square, including every nilpotent correction and the incidence-zero locus.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "U" => W.map f
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "hr'" => polynomialRootEquation_coefficient f W b3 b4 b6 r hr
local notation "F₀" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "F₁" => polynomialNodeForwardBase U (f s) (f b3) (f b4) (f b6)
  (r.map f) hr' J hJ hrJ (hf h3)
local notation "g" => nodeOpenCoefficientRingMap f W s
local notation "c" => coefficientRingMap f W s b3 b4 b6
local notation "e₀" => initialReflection W s b3 b4 b6
local notation "e₁" => initialReflection U (f s) (f b3) (f b4) (f b6)

/-- Every original reflected function commutes with the full initial coefficient map. -/
theorem polynomialOppositeNodeForward_coefficient :
    (g).comp ((F₀).toRingHom.comp (e₀).toRingEquiv.toRingHom) =
      ((F₁).toRingHom.comp (e₁).toRingEquiv.toRingHom).comp c := by
  rw [← RingHom.comp_assoc, polynomialNodeForwardBase_coefficient,
    RingHom.comp_assoc, initialReflection_coefficient, ← RingHom.comp_assoc]

/-- The opposite full node chart has its original coefficient square. -/
@[reassoc] theorem polynomialOppositeNodeChart_coefficient :
    Spec.map (CommRingCat.ofHom g) ≫
      polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3 =
        polynomialOppositeNodeChart U (f s) (f b3) (f b4) (f b6) (r.map f)
          hr' J hJ hrJ (hf h3) ≫ Spec.map (CommRingCat.ofHom c) := by
  rw [polynomialOppositeNodeChart_eq_spec, polynomialOppositeNodeChart_eq_spec]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h))
    (polynomialOppositeNodeForward_coefficient f W s b3 b4 b6 r hr I J hf hI hJ hrI h3)

end FLT.Mazur.WeierstrassModificationX
