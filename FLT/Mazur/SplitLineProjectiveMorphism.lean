/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLinePrincipalPoints
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the projective point of an actual split vector

An actual retraction makes the coordinate principal opens cover the affine
scheme. Their normalized image points glue to a genuine projective morphism.
The morphism recovers the original point on every coordinate principal open
and lies over the canonical coefficient spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLinePrincipalPoints
open NormalizedSectionLine ProjectiveSpace
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u}
variable (v : ι → Γ(X, ⊤))

/-- The actual two-coordinate intersection is affine. -/
instance intersection_affine (i j : ι) :
    IsAffine (X.basicOpen (v i) ⊓ X.basicOpen (v j)).toScheme := by
  rw [← X.basicOpen_mul]
  infer_instance

/-- The local normalized points agree on the actual coordinate-open intersection. -/
lemma point_inf (i j : ι) :
    X.homOfLE (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) ≫
        point v i (X.basicOpen (v i)) le_rfl =
      X.homOfLE inf_le_right ≫ point v j (X.basicOpen (v j)) le_rfl := by
  rw [point_restrict, point_restrict]
  exact point_eq v i j _ _ _

/-- The actual local points agree on the categorical intersections used for scheme gluing. -/
lemma point_compatible (i j : ι) :
    Limits.pullback.fst (X.basicOpen (v i)).ι (X.basicOpen (v j)).ι ≫
        point v i (X.basicOpen (v i)) le_rfl =
      Limits.pullback.snd (X.basicOpen (v i)).ι (X.basicOpen (v j)).ι ≫
        point v j (X.basicOpen (v j)) le_rfl := by
  apply (cancel_epi (isPullback_opens_inf
    (X.basicOpen (v i)) (X.basicOpen (v j))).isoPullback.hom).mp
  simpa only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd] using point_inf v i j

variable [Finite ι] (r : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (hr : r v = 1)

/-- The actual coordinate principal-open cover constructed from the retraction. -/
def openCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι
    (fun i ↦ (X.basicOpen (v i)).toScheme) (fun i ↦ (X.basicOpen (v i)).ι)
    (fun x ↦ by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
        (show x ∈ ⨆ i, X.basicOpen (v i) by rw [cover v r hr]; trivial)
      exact ⟨i, ⟨x, hi⟩, rfl⟩) (fun _ ↦ inferInstance)

/-- The projective morphism of a split vector, with no global invertible-coordinate assumption. -/
def morphism : X ⟶ space Γ(X, ⊤) ι :=
  (openCover v r hr).glueMorphisms
    (fun i ↦ point v i (X.basicOpen (v i)) le_rfl) (point_compatible v)

/-- The glued morphism recovers the original normalized point on each principal open. -/
@[reassoc]
lemma ι_morphism (i : ι) :
    (X.basicOpen (v i)).ι ≫ morphism v r hr = point v i (X.basicOpen (v i)) le_rfl :=
  (openCover v r hr).ι_glueMorphisms _ _ i

/-- Its coordinate charts determine the glued morphism uniquely. -/
lemma morphism_unique (p : X ⟶ space Γ(X, ⊤) ι)
    (hp : ∀ i, (X.basicOpen (v i)).ι ≫ p = point v i (X.basicOpen (v i)) le_rfl) :
    p = morphism v r hr := by
  apply (openCover v r hr).hom_ext
  intro i
  exact (hp i).trans (ι_morphism v r hr i).symm

/-- The constructed projective morphism is over the original coefficient spectrum. -/
lemma morphism_baseProjection : morphism v r hr ≫ baseProjection Γ(X, ⊤) ι =
    X.isoSpec.hom := by
  apply (openCover v r hr).hom_ext
  intro i
  change ι at i
  change (X.basicOpen (v i)).ι ≫ (morphism v r hr ≫ baseProjection Γ(X, ⊤) ι) =
    (X.basicOpen (v i)).ι ≫ X.isoSpec.hom
  rw [ι_morphism_assoc]
  unfold point affineGeneratorPoint affineSectionLinePoint
  rw [Category.assoc, sectionLinePoint_baseProjection]
  exact Scheme.isoSpec_hom_naturality _

end FLT.Mazur.SplitLinePrincipalPoints
