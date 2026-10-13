/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OverCoproductSchemeDescent
public import FLT.Mazur.CyclicPinchingReflection
public import FLT.Mazur.ProjectiveLineCoefficientEndpoints
public import FLT.Mazur.ProjectiveLineScaledEndpointReversal

/-!
# Semilinear scaled reflection on the original pinching sources

Each complete component changes coefficients before the specified scaled
reciprocal. Nodes retain the same coefficient map, and branches exchange labels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {n : ℕ} [NeZero n]
  (f : K →+* K) (c : Fin n → Kˣ)
local notation "q" => Spec.map (CommRingCat.ofHom f)

/-- The full source parameter changes coefficients before applying its original reciprocal. -/
def semilinearScaledParameter (i : Fin n) : ProjectiveLine.scheme K ⟶
    ProjectiveLine.scheme K :=
  ProjectiveLine.coefficientMap f ≫ ProjectiveLine.scaledEndpointReversal K (c i)

omit [NeZero n] in
/-- Every parameter retains the genuine coefficient change. -/
@[reassoc] theorem semilinearScaledParameter_structure (i : Fin n) :
    semilinearScaledParameter f c i ≫ ProjectiveLine.toBase K =
      ProjectiveLine.toBase K ≫ q := by
  rw [semilinearScaledParameter, Category.assoc,
    ProjectiveLine.scaledEndpointReversal_toBase, ProjectiveLine.coefficientMap_toBase]

omit [NeZero n] in
/-- The full original zero branch goes to infinity with its actual coefficient map. -/
@[reassoc] theorem semilinearScaledParameter_zero (i : Fin n) :
    ProjectiveLine.zero K ≫ semilinearScaledParameter f c i =
      q ≫ ProjectiveLine.infinity K := by
  rw [semilinearScaledParameter, ProjectiveLine.zero_coefficientMap_assoc,
    ProjectiveLine.zero_scaledEndpointReversal]

omit [NeZero n] in
/-- The opposite full branch goes to zero with the same coefficient map. -/
@[reassoc] theorem semilinearScaledParameter_infinity (i : Fin n) :
    ProjectiveLine.infinity K ≫ semilinearScaledParameter f c i =
      q ≫ ProjectiveLine.zero K := by
  rw [semilinearScaledParameter, ProjectiveLine.infinity_coefficientMap_assoc,
    ProjectiveLine.infinity_scaledEndpointReversal]

/-- Scaled semilinear reflection on the entire original component coproduct. -/
def semilinearScaledComponents : (components K n).left ⟶ (components K n).left :=
  OverCoproductScheme.desc (fun _ : Fin n => component K)
    (fun i => semilinearScaledParameter f c i ≫ (componentι K n (reflectIndex i)).left)

/-- Semilinear reflection on the entire original node coproduct. -/
def semilinearReflectionNodes : (nodes K n).left ⟶ (nodes K n).left :=
  OverCoproductScheme.desc (fun _ : Fin n => point K)
    (fun i => q ≫ (nodeι K n (reflectNodeIndex i)).left)

/-- Semilinear reflection exchanges both actual branches over every reflected node. -/
def semilinearReflectionBranches : (branches K n).left ⟶ (branches K n).left :=
  OverCoproductScheme.desc (fun _ : Fin n × Bool => point K)
    (fun ib => q ≫ (branchι K n (reflectNodeIndex ib.1) (!ib.2)).left)

/-- Every full component retains its specified scaled reciprocal and reflected index. -/
@[reassoc] theorem componentι_semilinearScaledComponents (i : Fin n) :
    (componentι K n i).left ≫ semilinearScaledComponents f c =
      semilinearScaledParameter f c i ≫ (componentι K n (reflectIndex i)).left :=
  OverCoproductScheme.ι_desc _ _ i

/-- The whole node summand retains its reflected position and coefficient morphism. -/
@[reassoc] theorem nodeι_semilinearReflectionNodes (i : Fin n) :
    (nodeι K n i).left ≫ semilinearReflectionNodes f =
      q ≫ (nodeι K n (reflectNodeIndex i)).left :=
  OverCoproductScheme.ι_desc _ _ i

/-- Both ordered branches retain their exact exchanged labels. -/
@[reassoc] theorem branchι_semilinearReflectionBranches (i : Fin n) (b : Bool) :
    (branchι K n i b).left ≫ semilinearReflectionBranches f =
      q ≫ (branchι K n (reflectNodeIndex i) (!b)).left :=
  OverCoproductScheme.ι_desc _ _ (i, b)

omit [NeZero n] in
/-- The original zero leg on underlying schemes. -/
@[reassoc] theorem branchι_toComponents_zero_left (hn : 0 < n) (i : Fin n) :
    (branchι K n i false).left ≫ (toComponents K n hn).left =
      ProjectiveLine.zero K ≫ (componentι K n i).left :=
  congrArg (fun t => t.left) (branchι_toComponents_zero K n hn i)

omit [NeZero n] in
/-- The original infinity leg on underlying schemes. -/
@[reassoc] theorem branchι_toComponents_infinity_left (hn : 0 < n) (i : Fin n) :
    (branchι K n i true).left ≫ (toComponents K n hn).left =
      ProjectiveLine.infinity K ≫ (componentι K n (next hn i)).left :=
  congrArg (fun t => t.left) (branchι_toComponents_infinity K n hn i)

omit [NeZero n] in
/-- Both original branches have the same unchanged node leg on underlying schemes. -/
@[reassoc] theorem branchι_toNodes_left (i : Fin n) (b : Bool) :
    (branchι K n i b).left ≫ (toNodes K n).left = (nodeι K n i).left :=
  congrArg (fun t => t.left) (branchι_toNodes K n i b)

/-- The full semilinear scaled source reflection respects the original component leg. -/
theorem semilinearScaled_toComponents (hn : 0 < n) :
    semilinearReflectionBranches f ≫ (toComponents K n hn).left =
      (toComponents K n hn).left ≫ semilinearScaledComponents f c := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin n × Bool => point K)
  rintro ⟨i, b⟩
  change (branchι K n i b).left ≫ _ = (branchι K n i b).left ≫ _
  rw [branchι_semilinearReflectionBranches_assoc]
  cases b
  · simp only [Bool.not_false, branchι_toComponents_infinity_left,
      branchι_toComponents_zero_left_assoc, componentι_semilinearScaledComponents,
      semilinearScaledParameter_zero_assoc, next_reflectNodeIndex]
  · simp only [Bool.not_true, branchι_toComponents_zero_left,
      branchι_toComponents_infinity_left_assoc, componentι_semilinearScaledComponents,
      semilinearScaledParameter_infinity_assoc, reflectIndex_next]

/-- The reflected full branch coproduct retains the original node map. -/
theorem semilinearReflection_toNodes :
    semilinearReflectionBranches f ≫ (toNodes K n).left =
      (toNodes K n).left ≫ semilinearReflectionNodes f := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin n × Bool => point K)
  rintro ⟨i, b⟩
  change (branchι K n i b).left ≫ _ = (branchι K n i b).left ≫ _
  rw [branchι_semilinearReflectionBranches_assoc, branchι_toNodes_left,
    branchι_toNodes_left_assoc, nodeι_semilinearReflectionNodes]

end FLT.Mazur.PolygonPinching
