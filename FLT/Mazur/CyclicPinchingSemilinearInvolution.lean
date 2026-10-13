/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CyclicPinchingSemilinearScaledSources
public import FLT.Mazur.ProjectiveLineSemilinearInvolution

/-!
# Involutions on the complete semilinear pinching sources

Involutive coefficients and reflection-invariant fixed scales restore every full
component, node and branch, including their original coproduct inclusions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {n : ℕ} [NeZero n]
  (f : K →+* K) (hf : f.comp f = RingHom.id K)
local notation "q" => Spec.map (CommRingCat.ofHom f)

include hf
omit [NeZero n] in
/-- The coefficient spectrum map squares to the identity. -/
@[reassoc] theorem semilinearCoefficient_involutive : q ≫ q = 𝟙 _ := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (f.comp f)) = _
  rw [hf]
  exact Spec.map_id _

variable (c : Fin n → Kˣ) (hc : ∀ i, Units.map f (c i) = c i)
  (hr : ∀ i, c (reflectIndex i) = c i)

include hc hr in
/-- The original full parameter at the reflected position is its inverse. -/
@[reassoc] theorem semilinearScaledParameter_reflected (i : Fin n) :
    semilinearScaledParameter f c i ≫ semilinearScaledParameter f c (reflectIndex i) =
      𝟙 _ := by
  simp only [semilinearScaledParameter, hr]
  exact ProjectiveLine.semilinearReciprocal_involutive f hf (c i) (hc i)

include hc hr in
/-- Reflection restores the whole original normalization coproduct. -/
@[reassoc] theorem semilinearScaledComponents_involutive :
    semilinearScaledComponents f c ≫ semilinearScaledComponents f c = 𝟙 _ := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin n => component K)
  intro i
  change (componentι K n i).left ≫ _ = (componentι K n i).left ≫ _
  rw [componentι_semilinearScaledComponents_assoc, componentι_semilinearScaledComponents,
    reflectIndex_reflectIndex, ← Category.assoc,
    semilinearScaledParameter_reflected f hf c hc hr]
  change 𝟙 _ ≫ (componentι K n i).left = (componentι K n i).left ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

/-- Reflection restores every full original node summand. -/
@[reassoc] theorem semilinearReflectionNodes_involutive :
    semilinearReflectionNodes (n := n) f ≫ semilinearReflectionNodes f = 𝟙 _ := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin n => point K)
  intro i
  change (nodeι K n i).left ≫ _ = (nodeι K n i).left ≫ _
  rw [nodeι_semilinearReflectionNodes_assoc, nodeι_semilinearReflectionNodes,
    reflectNodeIndex_reflectNodeIndex, semilinearCoefficient_involutive_assoc f hf,
    Category.comp_id]

/-- Reflection restores both labels and coefficients of every original branch. -/
@[reassoc] theorem semilinearReflectionBranches_involutive :
    semilinearReflectionBranches (n := n) f ≫ semilinearReflectionBranches f = 𝟙 _ := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin n × Bool => point K)
  rintro ⟨i, b⟩
  change (branchι K n i b).left ≫ _ = (branchι K n i b).left ≫ _
  rw [branchι_semilinearReflectionBranches_assoc, branchι_semilinearReflectionBranches,
    reflectNodeIndex_reflectNodeIndex, Bool.not_not,
    semilinearCoefficient_involutive_assoc f hf, Category.comp_id]

end FLT.Mazur.PolygonPinching
