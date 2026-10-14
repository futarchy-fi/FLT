/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecializationTransport

/-!
# Mapping evaluated models into the actual coefficient overlap

A coefficient point of an overlap supplies a map from the whole specialized
model into each overlap pullback. The original transport exchanges these maps
by the independently defined chosen-root change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (r : S) (v : T) (j : ℕ) (hj : j ≤ n) (f : S →ₐ[R] T)
  {Z : Scheme.{u}} (a : Z ⟶ Spec (.of S)) (e : Spec (.of T) ⟶ Z)
  (he : e ≫ a = Spec.map (CommRingCat.ofHom f.toRingHom))
local notation "gS" => coefficientShearGluedStructure hπ data S r j hj
local notation "gT" => coefficientShearGluedStructure hπ data T v j hj
local notation "pS" => coefficientShearGluedProjection hπ data S r j hj
local notation "M" => coefficientShearSpecialization hπ data S T r v j hj f

/-- The full evaluated equation model maps into the specified actual coefficient overlap. -/
def coefficientShearSpecializationOverlapLift :
    coefficientShearGlued hπ data T v j hj ⟶ pullback a gS :=
  pullback.lift (gT ≫ e) M (by
    rw [Category.assoc, he, coefficientShearSpecialization_structure])
local notation "L" => coefficientShearSpecializationOverlapLift hπ data S T r v j hj f a e he

/-- The overlap point is exactly the original coefficient point of the evaluated model. -/
@[reassoc] theorem coefficientShearSpecializationOverlapLift_structure :
    L ≫ pullback.fst a gS = gT ≫ e := pullback.lift_fst _ _ _

/-- The other leg retains the actual complete-model specialization. -/
@[reassoc] theorem coefficientShearSpecializationOverlapLift_model :
    L ≫ pullback.snd a gS = M := pullback.lift_snd _ _ _

variable (w : T) (g : S →ₐ[R] T) (b : Z ⟶ Spec (.of S))
  (hb : e ≫ b = Spec.map (CommRingCat.ofHom g.toRingHom))
  (hab : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    b ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
local notation "L'" => coefficientShearSpecializationOverlapLift hπ data S T r w j hj g b e hb
local notation "C" => coefficientShearRootChange hπ data T v w j hj

/-- The actual overlap transport changes precisely the independently chosen model root. -/
@[reassoc] theorem coefficientShearSpecializationOverlapLift_transport :
    L ≫ (coefficientShearTransport hπ data S r j hj a b hab).hom = (C).hom ≫ L' := by
  apply CartesianCoefficientTransport.hom_ext
    (coefficientShearGlued_isPullback hπ data S r j hj).flip b
  · simp only [Category.assoc, coefficientShearTransport_structure,
      coefficientShearSpecializationOverlapLift_structure,
      coefficientShearRootChange_structure_assoc]
  · simp only [Category.assoc, coefficientShearTransport_projection,
      coefficientShearSpecializationOverlapLift_model_assoc,
      coefficientShearSpecialization_projection, coefficientShearRootChange_projection]

end FLT.Mazur.WeierstrassDividedDepth
