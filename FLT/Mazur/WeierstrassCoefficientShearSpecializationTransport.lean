/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecializationCartesian
public import FLT.Mazur.WeierstrassCoefficientShearSpecializationComposition
public import FLT.Mazur.WeierstrassCoefficientShearTransport

/-!
# Actual coefficient transport between whole chosen-root specializations

The cartesian specialization squares identify each complete equation model with
its coefficient pullback. Under these identifications, the original overlap
transport is exactly the independently constructed change of shear parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (r : S) (v : T) (j : ℕ) (hj : j ≤ n) (f : S →ₐ[R] T)
local notation "gS" => coefficientShearGluedStructure hπ data S r j hj
local notation "gT" => coefficientShearGluedStructure hπ data T v j hj
local notation "a" => Spec.map (CommRingCat.ofHom f.toRingHom)
local notation "pS" => coefficientShearGluedProjection hπ data S r j hj
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "qT" => Spec.map (CommRingCat.ofHom (algebraMap R T))

/-- The whole specialized equation gluing is the actual pullback along its coefficient map. -/
def coefficientShearSpecializationPullbackIso :
    coefficientShearGlued hπ data T v j hj ≅ pullback a gS :=
  (coefficientShearSpecialization_isPullback hπ data S T r v j hj f).flip.isoPullback
local notation "E" => coefficientShearSpecializationPullbackIso hπ data S T r v j hj f

/-- The pullback identification keeps the entire coefficient structure. -/
@[reassoc] theorem coefficientShearSpecializationPullbackIso_structure :
    (E).hom ≫ pullback.fst a gS = gT :=
  (coefficientShearSpecialization_isPullback hπ data S T r v j hj f).flip.isoPullback_hom_fst

/-- The other leg is the actual specialization of the original equation model. -/
@[reassoc] theorem coefficientShearSpecializationPullbackIso_model :
    (E).hom ≫ pullback.snd a gS =
      coefficientShearSpecialization hπ data S T r v j hj f :=
  (coefficientShearSpecialization_isPullback hπ data S T r v j hj f).flip.isoPullback_hom_snd

omit [IsDomain R] [IsBezout R] in
/-- Every coefficient algebra map lies over the same original integral base. -/
theorem coefficientShearSpecialization_base : a ≫ qS = qT := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext f.commutes)

variable (w : T) (g : S →ₐ[R] T)
local notation "b" => Spec.map (CommRingCat.ofHom g.toRingHom)
local notation "F" => coefficientShearSpecializationPullbackIso hπ data S T r w j hj g
local notation "hfg" => (coefficientShearSpecialization_base S T f).trans
  (coefficientShearSpecialization_base S T g).symm
local notation "M" => coefficientShearTransport hπ data S r j hj a b hfg
local notation "C" => coefficientShearRootChange hπ data T v w j hj

/-- Original coefficient transport identifies the full independently sheared models. -/
@[reassoc] theorem coefficientShearSpecializationPullbackIso_transport :
    (E).hom ≫ (M).hom = (C).hom ≫ (F).hom := by
  apply CartesianCoefficientTransport.hom_ext
    (coefficientShearGlued_isPullback hπ data S r j hj).flip b
  · rw [Category.assoc, coefficientShearTransport_structure,
      coefficientShearSpecializationPullbackIso_structure, Category.assoc,
      coefficientShearSpecializationPullbackIso_structure, coefficientShearRootChange_structure]
  · simp only [Category.assoc, coefficientShearTransport_projection,
      coefficientShearSpecializationPullbackIso_model_assoc,
      coefficientShearSpecialization_projection, coefficientShearRootChange_projection]

/-- Conjugating the actual overlap comparison recovers the original whole-model root change. -/
theorem coefficientShearSpecialization_transport_rootChange :
    (E).hom ≫ (M).hom ≫ (F).inv = (C).hom := by
  rw [← Category.assoc, coefficientShearSpecializationPullbackIso_transport,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
