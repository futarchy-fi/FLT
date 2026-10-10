/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeHomogeneousRetract
public import FLT.Mazur.IdealAdicRelativePushforwardSerreBound
public import FLT.Mazur.PrincipalSectionExtension

/-!
# A Serre bound uniform over the actual homogeneous coefficients

The geometric O_X-linear homogeneous retractions survive tensoring by
any line power. The total pushforward Serre bound therefore kills every
positive cohomology of every homogeneous coefficient with one twist bound.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open ModuleSheafTensor ModuleLineBundleTensorPullback

namespace FLT.Mazur.IdealAdicGradedPullback

/-- A split inclusion transfers vanishing in any cohomological degree. -/
lemma moduleH_subsingleton_of_split {X : Scheme} {M N : X.Modules}
    (i : M ⟶ N) (p : N ⟶ M) (h : i ≫ p = 𝟙 M) (q : ℕ)
    (hz : Subsingleton (ModuleH N q)) : Subsingleton (ModuleH M q) := by
  have hi : Function.LeftInverse (moduleHMap p q) (moduleHMap i q) := by
    intro x
    have he := LinearMap.congr_fun (moduleHMap_comp i p q) x
    rw [h, moduleHMap_id] at he
    exact he.symm
  exact ⟨fun x y ↦ hi.injective (hz.elim _ _)⟩

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeHomogeneousInclusion relativeHomogeneousProjection
attribute [local irreducible] relativeDescendedCoefficientPushforward

/-- Tensoring preserves the actual geometric homogeneous retraction. -/
lemma relativeHomogeneousTwist_retraction (n : ℕ) (T : X.Modules) :
    ModuleSheafTensor.map (relativeHomogeneousInclusion J f n) (𝟙 T) ≫
        ModuleSheafTensor.map (relativeHomogeneousProjection J f n) (𝟙 T) =
      𝟙 (tensor (idealGraded (J.comap f) n) T) := by
  rw [← ModuleSheafTensor.map_comp, relativeHomogeneousInclusion_projection, Category.id_comp,
    ModuleSheafTensor.map_id]

/-- One twist bound kills all positive cohomology in every original homogeneous degree. -/
theorem idealGraded_uniform_serreBound [IsProper f] {L : X.Modules} (hL : AmpleLineBundle L) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n q : ℕ,
      Subsingleton (ModuleH (tensor (idealGraded (J.comap f) n) (tensorPower L m)) (q + 1)) := by
  obtain ⟨N, hN⟩ := relativeDescendedPushforward_serreBound J f hL
  refine ⟨N, fun m hm n q ↦ ?_⟩
  exact moduleH_subsingleton_of_split
    (ModuleSheafTensor.map (relativeHomogeneousInclusion J f n) (𝟙 (tensorPower L m)))
    (ModuleSheafTensor.map (relativeHomogeneousProjection J f n) (𝟙 (tensorPower L m)))
    (relativeHomogeneousTwist_retraction J f n (tensorPower L m)) (q + 1) (hN m hm q)

/-- The same bound applies to the actual image-filtration coefficients of each line power. -/
theorem gradedLine_uniform_serreBound [IsProper f] {L : X.Modules} (hL : AmpleLineBundle L) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n q : ℕ,
      let _ := (hL.2.1.tensorPower m).isFinitePresentation
      Subsingleton (ModuleH (graded (J.comap f) (tensorPower L m) n) (q + 1)) := by
  obtain ⟨N, hN⟩ := idealGraded_uniform_serreBound J f hL
  refine ⟨N, fun m hm n q ↦ ?_⟩
  let _ := (hL.2.1.tensorPower m).isFinitePresentation
  exact @moduleH_subsingleton_of_iso X _ _
    (gradedLineTwistIso (J.comap f) (tensorPower L m) (hL.2.1.tensorPower m) n) (q + 1)
    (hN m hm n q)

end FLT.Mazur.IdealAdicGradedPullback
