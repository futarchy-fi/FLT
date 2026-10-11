/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedAcyclicFppfDetection
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Locally acyclic actual Picard-sheaf sections without an original section

The local acyclic subsheaf consists of actual Picard-sheaf sections with
acyclic relative representatives on an fppf cover. On every globally
represented section, membership is exactly the intrinsic geometric condition.
Global representability of all members is a separate descent problem.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f]

/-- Actual sections which fppf locally have geometric acyclic rank-one representatives. -/
def localGeometricAcyclicFppfSubfunctor :
    Subfunctor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat) :=
  (geometricAcyclicFppfSubfunctor f).sheafify (Scheme.fppfTopology.over S)

/-- Local membership gives an actual small fppf family of acyclic representatives. -/
theorem localGeometricAcyclicFppf_exists_cover (T : Over S)
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (hs : s ∈ (localGeometricAcyclicFppfSubfunctor f).obj (op T)) :
    ∃ 𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left,
      ∀ i, ∃ c, RelativeGeometricAcyclicRankOne
        (Limits.pullback.snd f (relativeCoverMember T 𝒰 i).hom) c ∧
        relativeFppfClass f _ c =
          (relativeFppfSheaf f).obj.map (relativeCoverArrow T 𝒰 i).op s :=
  relativeFppf_exists_cover _ hs

/-- An actual cover of acyclic representatives certifies membership of the local subsheaf. -/
theorem localGeometricAcyclicFppf_of_cover (T : Over S)
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    (h : ∀ i, (relativeFppfSheaf f).obj.map (relativeCoverArrow T 𝒰 i).op s ∈
      (geometricAcyclicFppfSubfunctor f).obj (op (relativeCoverMember T 𝒰 i))) :
    s ∈ (localGeometricAcyclicFppfSubfunctor f).obj (op T) := by
  change (geometricAcyclicFppfSubfunctor f).sieveOfSection s ∈
    (Scheme.fppfTopology.over S) T
  have hcov : Sieve.ofArrows (relativeCoverMember T 𝒰) (relativeCoverArrow T 𝒰) ∈
      (Scheme.fppfTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.generate_mem_toGrothendieck 𝒰.mem₀
  apply (Scheme.fppfTopology.over S).superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact h i

/-- On actual relative classes, local sheaf membership is the intrinsic geometric condition. -/
theorem localGeometricAcyclicFppf_class_iff (T : Over S)
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    relativeFppfClass f T c ∈ (localGeometricAcyclicFppfSubfunctor f).obj (op T) ↔
      RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.hom) c := by
  constructor
  · intro hc
    obtain ⟨𝒰, h𝒰⟩ := localGeometricAcyclicFppf_exists_cover f T _ hc
    apply (relativeGeometricAcyclicRankOne_fppf_iff f T 𝒰 c).mpr
    intro i
    apply (unpointed_geometricAcyclicFppf_class_iff f _ _).mp
    rw [← relativeFppfClass_naturality]
    exact h𝒰 i
  · intro hc
    exact (geometricAcyclicFppfSubfunctor f).le_sheafify _ _ ⟨c, hc, rfl⟩

/-- The local acyclic locus satisfies effective fppf descent on all tests. -/
theorem localGeometricAcyclicFppf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (localGeometricAcyclicFppfSubfunctor f).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply Subfunctor.sheafify_isSheaf
  rw [← isSheaf_iff_isSheaf_of_type]
  exact ((sheafCompose (Scheme.fppfTopology.over S) (forget CommGrpCat.{1})).obj
    (relativeFppfSheaf f)).property

/-- The local acyclic subsheaf with the original Picard section values. -/
def localGeometricAcyclicFppfSheaf : Sheaf (Scheme.fppfTopology.over S) (Type 1) :=
  ⟨_, localGeometricAcyclicFppf_isSheaf f⟩

end FLT.Mazur.CartierAbel
