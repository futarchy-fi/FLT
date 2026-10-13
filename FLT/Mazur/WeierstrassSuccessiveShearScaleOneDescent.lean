/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneIncidence
public import FLT.Mazur.WeierstrassModificationXFullFiberMarkedDescent

/-!
# Descent on the complete original scale-one tensor equation

Compatible maps from the entire original conic and incidence line descend
uniquely to the original tensor chart, including both intersection sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S b6
local notation "T" => ScalarExtension W s π b3 b4 b6 S
local notation "e" => tensorShearScaleOneFiberEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- The complete scale-one fiber normal form preserves the entire original tensor chart. -/
def tensorShearScaleOneFiberIso : Spec (.of (FiberCoordinate a c)) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "E" => tensorShearScaleOneFiberIso W s π b3 b4 b6 S r hs hp h3 h4 hr
local notation "C₀" => tensorShearScaleOneConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr
local notation "L" => Spec.map (CommRingCat.ofHom
  (tensorShearScaleOneIncidenceMap W s π b3 b4 b6 S r hs hp h3 h4 hr).toRingHom)

/-- The entire original conic factors through the full normal-form comparison. -/
@[reassoc] theorem tensorShearScaleOneFiberIso_conic :
    fiberConicImmersion a c ≫ (E).hom = C₀ := by
  rw [tensorShearScaleOneConicImmersion_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The complete original incidence line factors through the same comparison. -/
@[reassoc] theorem tensorShearScaleOneFiberIso_incidence :
    fiberIncidenceImmersion a c ≫ (E).hom = L := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  {Y : Scheme.{u}} (f : Spec (.of (ConicCoordinate
    (rootShearCurve (W.map (algebraMap R S)) r).a₁ (algebraMap R S b6))) ⟶ Y)
  (g : ProjectiveLine.chart S ⟶ Y)
  (w₁ : Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁ (algebraMap R S b6) ha).toRingHom) ≫ f =
      ProjectiveLine.chartZero S ≫ g)
  (w₂ : Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁ (algebraMap R S b6) ha).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom (aeval
        (-(rootShearCurve (W.map (algebraMap R S)) r).a₁)).toRingHom) ≫ g)

/-- Both compatible full component maps descend to the original tensor equation. -/
@[irreducible] def tensorShearScaleOneDesc : Spec (.of T) ⟶ Y :=
  (E).inv ≫ fullFiberMarkedDesc a c ha f g w₁ w₂
local notation "D" => tensorShearScaleOneDesc W s π b3 b4 b6 S r hs hp h3 h4 hr ha f g w₁ w₂

/-- The descended map retains the entire full-fiber descent. -/
@[reassoc] theorem tensorShearScaleOneDesc_normal :
    (E).hom ≫ D = fullFiberMarkedDesc a c ha f g w₁ w₂ := by
  rw [tensorShearScaleOneDesc, Iso.hom_inv_id_assoc]

/-- Restriction to the original whole conic recovers its given map. -/
@[reassoc] theorem tensorShearScaleOneDesc_conic : C₀ ≫ D = f := by
  rw [← tensorShearScaleOneFiberIso_conic, Category.assoc,
    tensorShearScaleOneDesc_normal, fullFiberMarkedDesc_conic]

/-- Restriction to the original entire affine line recovers its given map. -/
@[reassoc] theorem tensorShearScaleOneDesc_incidence : L ≫ D = g := by
  rw [← tensorShearScaleOneFiberIso_incidence, Category.assoc,
    tensorShearScaleOneDesc_normal, fullFiberMarkedDesc_incidence]

/-- These two original full restrictions uniquely determine the tensor-chart map. -/
theorem tensorShearScaleOneDesc_unique (m : Spec (.of T) ⟶ Y)
    (hf : C₀ ≫ m = f) (hg : L ≫ m = g) : m = D := by
  apply (cancel_epi (E).hom).mp
  apply fullFiber_components_hom_ext a c ha
  · rw [tensorShearScaleOneFiberIso_incidence_assoc, hg,
      tensorShearScaleOneFiberIso_incidence_assoc, tensorShearScaleOneDesc_incidence]
  · rw [tensorShearScaleOneFiberIso_conic_assoc, hf,
      tensorShearScaleOneFiberIso_conic_assoc, tensorShearScaleOneDesc_conic]

end FLT.Mazur.WeierstrassSuccessiveX
