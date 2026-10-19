/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalKernelTower

/-!
# Extending full section covers to another original local cubic model

Base change the given sections and identify the resulting cover with the
second model's own kernel. The sections retain their original source maps,
openness, and coverage of every scheme point and residue branch.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassLocalKernelCoverExtension
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
variable (r : Spec (.of K) ⟶ localGenericKernel E W C hC i)
  (hr : r ≫ localGenericKernelInclusion E W C hC i ≫
    integralCurveStructure (W.map (algebraMap A K)) = 𝟙 _)

/-- The actual extended section on the second model's original kernel. -/
def sectionMap : Spec (.of L) ⟶ localGenericKernel E V D hD i :=
  WeierstrassLocalKernelTower.sectionMap E W V C D hC hD i
    (SectionCoverBaseChange.sectionMap (f) k r hr)

/-- Each extended section retains its projection to the first kernel. -/
@[reassoc] theorem sectionMap_comparison :
    sectionMap E W V C D hC hD i r hr ≫
      WeierstrassLocalKernelTower.comparison E W V C D hC hD i = k ≫ r := by
  rw [sectionMap, WeierstrassLocalKernelTower.sectionMap_original,
    SectionCoverBaseChange.sectionMap_fst]

/-- The original kernel scheme projection is retained after both transports. -/
@[reassoc] theorem sectionMap_original :
    sectionMap E W V C D hC hD i r hr ≫ localGenericKernelOriginal E V D hD i =
      k ≫ r ≫ localGenericKernelOriginal E W C hC i := by
  rw [← WeierstrassLocalKernelTower.comparison_original E W V C D hC hD i,
    ← Category.assoc, sectionMap_comparison, Category.assoc]

/-- The transferred morphism is a section of the exact new kernel structure map. -/
@[reassoc] theorem sectionMap_structure :
    sectionMap E W V C D hC hD i r hr ≫ f' = 𝟙 _ := by
  rw [sectionMap, WeierstrassLocalKernelTower.sectionMap_structure,
    SectionCoverBaseChange.sectionMap_snd]

/-- Openness survives the extension and the change of the local equation. -/
theorem sectionMap_isOpenImmersion [IsOpenImmersion r] :
    IsOpenImmersion (sectionMap E W V C D hC hD i r hr) := by
  let _ := IsOpenImmersion.of_isPullback
    (SectionCoverBaseChange.sectionMap_isPullback (f) k r hr).flip inferInstance
  exact WeierstrassLocalKernelTower.sectionMap_isOpenImmersion E W V C D hC hD i _

/-- The full original cover extends to the full new kernel, with no residue branches lost. -/
theorem sectionMap_covers {J : Type} (r : J → (Spec (.of K) ⟶
    localGenericKernel E W C hC i)) (hr : ∀ j, r j ≫ f = 𝟙 _)
    (hc : ∀ x : localGenericKernel E W C hC i, ∃ j z, r j z = x) :
    ∀ x : localGenericKernel E V D hD i,
      ∃ j z, sectionMap E W V C D hC hD i (r j) (hr j) z = x := by
  apply WeierstrassLocalKernelTower.sectionMap_covers
  have hc' : ∀ x : localGenericKernel E W C hC i, ∃ j, r j ((f) x) = x := by
    intro x
    obtain ⟨j, z, rfl⟩ := hc x
    refine ⟨j, ?_⟩
    change r j ((r j ≫ f) z) = _
    rw [hr j]
    rfl
  intro x
  obtain ⟨j, hj⟩ := SectionCoverBaseChange.covers (f) k r hr hc' x
  exact ⟨j, pullback.snd (f) k x, hj⟩

end FLT.Mazur.WeierstrassLocalKernelCoverExtension
