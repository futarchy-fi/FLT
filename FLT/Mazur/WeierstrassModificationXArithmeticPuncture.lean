/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXStandardPunctureEquiv
public import FLT.Mazur.WeierstrassModificationXArithmeticNodeBoundary

/-!
# The full initial standard puncture over the original arithmetic quotients

The complete Laurent boundary identifies with D(p), including its corrected
reciprocal incidence, and factors the actual full arithmetic node restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "N" => NodalFiber.Coordinate (q s)
local notation "D" => Localization.Away (NodalFiber.p (q s))
local notation "L" => PolynomialNodeOpen (W.map q) (q s)

/-- The entire standard D(p) maps to the original full arithmetic node neighborhood. -/
def arithmeticInitialPunctureInclusion : Spec (.of D) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (initialNodeStandardPuncture (W.map q) (q s) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs)).toRingHom)

/-- Identify the original full initial Laurent boundary with the complete standard D(p). -/
def arithmeticInitialPunctureIso : Spec (.of Q[T;T⁻¹]) ≅ Spec (.of D) :=
  initialStandardPunctureIso (W.map q) (q s) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m hs)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
    (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)

/-- The actual arithmetic restriction is retained on every original node function. -/
@[reassoc] theorem arithmeticInitialPunctureIso_boundary :
    (arithmeticInitialPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6).hom ≫
      arithmeticInitialPunctureInclusion π m W s ha hs =
        arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs :=
  initialStandardPunctureIso_boundary ..

/-- The inverse comparison also retains the full original arithmetic node boundary. -/
@[reassoc] theorem arithmeticInitialPunctureIso_inv_boundary :
    (arithmeticInitialPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6).inv ≫
      arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs =
        arithmeticInitialPunctureInclusion π m W s ha hs := by
  rw [← arithmeticInitialPunctureIso_boundary, Iso.inv_hom_id_assoc]

/-- The inclusion in the full node neighborhood retains its standard node coordinates. -/
@[reassoc] theorem arithmeticInitialPunctureInclusion_node :
    arithmeticInitialPunctureInclusion π m W s ha hs ≫
      Spec.map (CommRingCat.ofHom (algebraMap N L)) =
        Spec.map (CommRingCat.ofHom (algebraMap N D)) := by
  rw [arithmeticInitialPunctureInclusion, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (initialNodeStandardPuncture_base (W.map q) (q s) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m hs))

/-- The standard initial puncture is an open of the actual full node neighborhood. -/
theorem arithmeticInitialPunctureInclusion_isOpenImmersion :
    IsOpenImmersion (arithmeticInitialPunctureInclusion π m W s ha hs) := by
  have h := arithmeticInitialPunctureInclusion_node π m W s ha hs
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap N D))) :=
    IsOpenImmersion.of_isLocalization (NodalFiber.p (q s))
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap N L))) :=
    IsOpenImmersion.of_isLocalization (NodalFiber.q (q s) + algebraMap Q N (W.map q).a₁)
  have hcomp : IsOpenImmersion (arithmeticInitialPunctureInclusion π m W s ha hs ≫
      Spec.map (CommRingCat.ofHom (algebraMap N L))) := by
    rw [h]
    infer_instance
  exact IsOpenImmersion.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap N L)))

/-- The full arithmetic Laurent boundary is an open immersion into its node neighborhood. -/
theorem arithmeticInitialNodeRestriction_isOpenImmersion :
    IsOpenImmersion
      (arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs) := by
  rw [← arithmeticInitialPunctureIso_boundary]
  let _ := arithmeticInitialPunctureInclusion_isOpenImmersion π m W s ha hs
  infer_instance

end FLT.Mazur.WeierstrassModificationX
