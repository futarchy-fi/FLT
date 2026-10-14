/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecializationOverlap
public import FLT.Mazur.WeierstrassCoefficientShearTangentRootEvaluation
public import FLT.Mazur.WeierstrassCoefficientShearTangentEffectiveDescent

/-!
# Chosen-root evaluation of the original effective tangent Cech comparison

Both evaluated roots give an actual point of the quadratic Cech scheme. Its
whole-model comparison is the independent root change, and compatible maps
retain this equality under the proved effective descent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r t : S)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (j : ℕ) (hj : j ≤ n)
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "root" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "er" => nodeTangentRootEvaluation W S r hr
local notation "et" => nodeTangentRootEvaluation W S t ht
local notation "q" => nodeTangentCover W
local notation "a" => pullback.fst q q
local notation "b" => pullback.snd q q
local notation "gA" => coefficientShearGluedStructure hπ data A root j hj

omit [IsDomain R] [IsBezout R] in
/-- Two actual root evaluations define a point of the original quadratic overlap. -/
def coefficientShearTangentRootCechPoint : Spec (.of S) ⟶ pullback q q :=
  pullback.lift (Spec.map (CommRingCat.ofHom (er).toRingHom))
    (Spec.map (CommRingCat.ofHom (et).toRingHom))
    ((coefficientShearSpecialization_base A S er).trans
      (coefficientShearSpecialization_base A S et).symm)
local notation "e" => coefficientShearTangentRootCechPoint S r t hr ht

/-- The entire first evaluated model maps into the actual first Cech model pullback. -/
def coefficientShearTangentRootCechFirst :=
  coefficientShearSpecializationOverlapLift hπ data A S root r j hj er a e
    (pullback.lift_fst _ _ _)
local notation "Lr" => coefficientShearTangentRootCechFirst hπ data S r t hr ht j hj

/-- The entire second evaluated model maps into the actual second Cech model pullback. -/
def coefficientShearTangentRootCechSecond :=
  coefficientShearSpecializationOverlapLift hπ data A S root t j hj et b e
    (pullback.lift_snd _ _ _)
local notation "Lt" => coefficientShearTangentRootCechSecond hπ data S r t hr ht j hj
local notation "M" => coefficientShearTransport hπ data A root j hj a b pullback.condition
local notation "C" => coefficientShearRootChange hπ data S r t j hj
local notation "Mr" => coefficientShearTangentRootSpecialization hπ data S r hr j hj
local notation "Mt" => coefficientShearTangentRootSpecialization hπ data S t ht j hj

/-- The actual effective Cech transport on the whole model evaluates to the original root change. -/
@[reassoc] theorem coefficientShearTangentRootCech_transport : Lr ≫ (M).hom = (C).hom ≫ Lt :=
  coefficientShearSpecializationOverlapLift_transport
    hπ data A S root r j hj er a e (pullback.lift_fst _ _ _)
    t et b (pullback.lift_snd _ _ _) pullback.condition

/-- Reconstruction identifies the evaluated comparison with the original integral Cech map. -/
@[reassoc] theorem coefficientShearTangentRootCech_original :
    Lr ≫ coefficientShearOverlapReconstruction hπ data A root j hj a ≫
        (finiteGlobalTangentCechIso hπ data j hj).hom =
      (C).hom ≫ Lt ≫ coefficientShearOverlapReconstruction hπ data A root j hj b := by
  rw [← coefficientShearTangentCech_reconstruction,
    ← Category.assoc, coefficientShearTangentRootCech_transport, Category.assoc]

/-- On companion roots the actual Cech comparison is the genuine integral tangent conjugation. -/
@[reassoc] theorem coefficientShearTangentRootCech_conjugation
    (hrt : r + t = -algebraMap R S W.a₁) :
    Lr ≫ (M).hom ≫ pullback.snd b gA =
      Mr ≫ coefficientShearTangentConjugation hπ data j hj := by
  rw [← Category.assoc, coefficientShearTangentRootCech_transport, Category.assoc,
    coefficientShearTangentRootSpecialization_conjugation hπ data S r hr j hj t ht hrt]
  exact congrArg ((C).hom ≫ ·)
    (coefficientShearSpecializationOverlapLift_model
      hπ data A S root t j hj et b e (pullback.lift_snd _ _ _))

/-- Every effectively compatible map agrees on the complete two evaluated root presentations. -/
theorem coefficientShearTangentRootCech_compatible {Y : Scheme}
    (k : coefficientShearGlued hπ data A root j hj ⟶ Y)
    (hk : pullback.snd a gA ≫ k = (M).hom ≫ pullback.snd b gA ≫ k) :
    Mr ≫ k = (C).hom ≫ Mt ≫ k := by
  obtain ⟨f, hf, _⟩ := coefficientShearTangentCech_existsUnique hπ data j hj k hk
  rw [← hf]
  simp only [coefficientShearTangentRootSpecialization,
    coefficientShearSpecialization_projection_assoc, coefficientShearRootChange_projection_assoc]

end FLT.Mazur.WeierstrassDividedDepth
