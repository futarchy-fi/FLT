/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialFiber
public import FLT.Mazur.WeierstrassModificationXFullFiberMarkedDescent

/-!
# Descent to the entire actual initial coefficient equation

Transfer the full marked incidence-conic descent through the coefficient
normal equivalence, without deleting the exceptional locus or its attachments.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "e" => coefficientShearNormalEquiv W (π ^ start)
  (data ⟨0, Nat.zero_lt_succ n⟩).b3 (data ⟨0, Nat.zero_lt_succ n⟩).b4
  (data ⟨0, Nat.zero_lt_succ n⟩).b6 S r hs h3 h4 hr

/-- The normal-form fiber identifies the actual entire initial atlas object. -/
def coefficientShearInitialEquationIso :
    Spec (.of (FiberCoordinate a c)) ≅ coefficientShearAtlasObject data S r j hj (.inl 2) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op

local notation "E" => coefficientShearInitialEquationIso data S r j hj hs h3 h4 hr

/-- The comparison recovers the actual initial chart map into the glued model. -/
@[reassoc] theorem coefficientShearInitialEquationIso_chart (hπ : π ≠ 0) :
    (E).hom ≫ coefficientShearGluedChart hπ data S r j hj (.inl 2) =
      coefficientShearInitialFiber hπ data S r j hj hs h3 h4 hr := rfl

omit [IsDomain R] [IsBezout R]

variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  {Y : Scheme.{u}}
  (f : Spec (.of (ConicCoordinate
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6))) ⟶ Y)
  (g : ProjectiveLine.chart S ⟶ Y)
  (w₁ : Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6) ha).toRingHom) ≫ f =
      ProjectiveLine.chartZero S ≫ g)
  (w₂ : Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6) ha).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom (aeval
        (-(rootShearCurve (W.map (algebraMap R S)) r).a₁) : S[X] →ₐ[S] S).toRingHom) ≫ g)

/-- The actual full coefficient equation receives the descended component maps. -/
@[irreducible] def coefficientShearInitialEquationDesc :
    coefficientShearAtlasObject data S r j hj (.inl 2) ⟶ Y :=
  (E).inv ≫ fullFiberMarkedDesc a c ha f g w₁ w₂

/-- Pulling back the descended equation map recovers the entire normal-form descent. -/
@[reassoc] theorem coefficientShearInitialEquationDesc_normal :
    (E).hom ≫ coefficientShearInitialEquationDesc data S r j hj hs h3 h4 hr ha f g w₁ w₂ =
      fullFiberMarkedDesc a c ha f g w₁ w₂ := by
  rw [coefficientShearInitialEquationDesc, Iso.hom_inv_id_assoc]

/-- The full original conic is retained in the actual coefficient equation. -/
@[reassoc] theorem coefficientShearInitialEquationDesc_conic :
    fiberConicImmersion a c ≫ (E).hom ≫
      coefficientShearInitialEquationDesc data S r j hj hs h3 h4 hr ha f g w₁ w₂ = f := by
  rw [coefficientShearInitialEquationDesc_normal, fullFiberMarkedDesc_conic]

/-- The full original incidence line is retained in the actual coefficient equation. -/
@[reassoc] theorem coefficientShearInitialEquationDesc_incidence :
    fiberIncidenceImmersion a c ≫ (E).hom ≫
      coefficientShearInitialEquationDesc data S r j hj hs h3 h4 hr ha f g w₁ w₂ = g := by
  rw [coefficientShearInitialEquationDesc_normal, fullFiberMarkedDesc_incidence]

/-- These entire component restrictions uniquely determine the actual equation map. -/
theorem coefficientShearInitialEquationDesc_unique
    (d : coefficientShearAtlasObject data S r j hj (.inl 2) ⟶ Y)
    (hf : fiberConicImmersion a c ≫ (E).hom ≫ d = f)
    (hg : fiberIncidenceImmersion a c ≫ (E).hom ≫ d = g) :
    d = coefficientShearInitialEquationDesc data S r j hj hs h3 h4 hr ha f g w₁ w₂ := by
  apply (cancel_epi (E).hom).mp
  rw [coefficientShearInitialEquationDesc_normal]
  apply fullFiber_components_hom_ext a c ha
  · rw [hg, fullFiberMarkedDesc_incidence]
  · rw [hf, fullFiberMarkedDesc_conic]

end FLT.Mazur.WeierstrassDividedDepth
