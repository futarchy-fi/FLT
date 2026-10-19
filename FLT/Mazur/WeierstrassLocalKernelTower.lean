/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalKernelCoefficientSquare
public import FLT.Mazur.CartesianSectionCoverTower

/-!
# The original local kernel through a tower of coefficient models

Both models are pulled back from the same original embedded scheme. Their
canonical comparison retains the original inclusion and transfers the full
rational section cover onto the second model's own local generic kernel.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassLocalKernelTower
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R K L A B : Type} [CommRing R] [CommRing K] [CommRing L]
  [CommRing A] [CommRing B] [Algebra R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L] [Algebra A K] [Algebra B L]
  (E : WeierstrassCurve R) (W : WeierstrassCurve A) (V : WeierstrassCurve B)
  (C : VariableChange K) (D : VariableChange L)
  (hC : C • E.map (algebraMap R K) = W.map (algebraMap A K))
  (hD : D • E.map (algebraMap R L) = V.map (algebraMap B L))
  {H : Scheme} (i : H ⟶ integralCurve E)
local notation "k" => Spec.map (CommRingCat.ofHom (algebraMap K L))
local notation "f" => localGenericKernelInclusion E W C hC i ≫
  integralCurveStructure (W.map (algebraMap A K))
local notation "f'" => localGenericKernelInclusion E V D hD i ≫
  integralCurveStructure (V.map (algebraMap B L))

/-- The second kernel's coefficient square retains the original scalar tower. -/
theorem outerSquare :
    IsPullback (localGenericKernelOriginal E V D hD i) (f')
      (i ≫ integralCurveStructure E)
      (k ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have he : Spec.map (CommRingCat.ofHom (algebraMap R L)) =
      k ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [IsScalarTower.algebraMap_eq R K L, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [← he]
  exact WeierstrassLocalKernelCoefficientSquare.isPullback E V D hD i

/-- The exact original source projection determines the tower comparison. -/
def comparison : localGenericKernel E V D hD i ⟶ localGenericKernel E W C hC i :=
  CartesianSectionCoverTower.comparison
    (WeierstrassLocalKernelCoefficientSquare.isPullback E W C hC i)
    (outerSquare E V D hD i)

/-- The comparison retains the map to the original embedded source scheme. -/
@[reassoc] theorem comparison_original :
    comparison E W V C D hC hD i ≫ localGenericKernelOriginal E W C hC i =
      localGenericKernelOriginal E V D hD i :=
  CartesianSectionCoverTower.comparison_original _ _

/-- The comparison retains the exact local coefficient map. -/
@[reassoc] theorem comparison_structure : comparison E W V C D hC hD i ≫ f = f' ≫ k :=
  CartesianSectionCoverTower.comparison_structure _ _

/-- The transported kernel is the full Cartesian coefficient extension of the first. -/
theorem comparison_isPullback :
    IsPullback (comparison E W V C D hC hD i) (f') (f) k :=
  CartesianSectionCoverTower.comparison_isPullback _ _

/-- Identify the canonical pullback with the second model's own original source kernel. -/
def baseChangeIso : localGenericKernel E V D hD i ≅ pullback (f) k :=
  (comparison_isPullback E W V C D hC hD i).isoPullback

/-- Transfer each actual rational section to the second local equation. -/
def sectionMap (r : Spec (.of L) ⟶ pullback (f) k) :
    Spec (.of L) ⟶ localGenericKernel E V D hD i :=
  CartesianSectionCoverTower.sectionMap
    (WeierstrassLocalKernelCoefficientSquare.isPullback E W C hC i)
    (outerSquare E V D hD i) r

/-- The original section's source projection is retained exactly. -/
@[reassoc] theorem sectionMap_original (r : Spec (.of L) ⟶ pullback (f) k) :
    sectionMap E W V C D hC hD i r ≫ comparison E W V C D hC hD i =
      r ≫ pullback.fst (f) k :=
  CartesianSectionCoverTower.sectionMap_original _ _ r

/-- The structure equation transfers to the actual local kernel inclusion. -/
@[reassoc] theorem sectionMap_structure (r : Spec (.of L) ⟶ pullback (f) k) :
    sectionMap E W V C D hC hD i r ≫ f' = r ≫ pullback.snd (f) k :=
  CartesianSectionCoverTower.sectionMap_structure _ _ r

/-- Open rational sections remain open after the canonical identification. -/
theorem sectionMap_isOpenImmersion (r : Spec (.of L) ⟶ pullback (f) k)
    [IsOpenImmersion r] : IsOpenImmersion (sectionMap E W V C D hC hD i r) :=
  CartesianSectionCoverTower.sectionMap_isOpenImmersion _ _ r

/-- Every point and residue branch of the second local kernel is covered. -/
theorem sectionMap_covers {J : Type} (r : J → (Spec (.of L) ⟶ pullback (f) k))
    (hc : ∀ x : (pullback (f) k : Scheme), ∃ j z, r j z = x) :
    ∀ x : localGenericKernel E V D hD i,
      ∃ j z, sectionMap E W V C D hC hD i (r j) z = x :=
  CartesianSectionCoverTower.sectionMap_covers _ _ r hc

end FLT.Mazur.WeierstrassLocalKernelTower
