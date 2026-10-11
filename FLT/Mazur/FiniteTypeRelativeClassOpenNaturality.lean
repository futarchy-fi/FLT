/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestRelativePicardOpen
public import FLT.Mazur.UnpointedAcyclicFppfDetection

/-!
# Intrinsic relative class opens on the big test site

The original test-space opens commute with all relative restriction maps.
Equality in the actual Picard sheaf preserves these opens, even when the
original family has no section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- The intrinsic class open on the original total space of a test. -/
abbrev finiteTypeRelativeClassOpen (T : Over (Spec (.of R)))
    (c : RelativePic (Limits.pullback.snd f T.hom)) : T.left.Opens :=
  finiteTypeTestRelativePicardOpen (IsPullback.of_hasPullback f T.hom) c

/-- Restricting a relative class pulls back its actual open. -/
theorem finiteTypeRelativeClassOpen_map {T U : Over (Spec (.of R))} (b : U ⟶ T)
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    finiteTypeRelativeClassOpen f U (relativeBaseMap f b c) =
      b.left ⁻¹ᵁ finiteTypeRelativeClassOpen f T c :=
  finiteTypeTestRelativePicardOpen_baseChange (IsPullback.of_hasPullback f T.hom)
    (relativeTotalMap_isPullback f b) c

/-- The class is geometrically acyclic of rank one exactly when its open is the whole test. -/
theorem finiteTypeRelativeClassOpen_eq_top (T : Over (Spec (.of R)))
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    finiteTypeRelativeClassOpen f T c = ⊤ ↔
      RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.hom) c := by
  obtain ⟨L, rfl⟩ := relativePic_exists_line (Limits.pullback.snd f T.hom) c
  rw [finiteTypeRelativeClassOpen, finiteTypeTestRelativePicardOpen_mk,
    relativeGeometricAcyclicRankOne_mk]
  change (⟨_, _⟩ : T.left.Opens) = ⊤ ↔ _
  rw [SetLike.ext'_iff]
  exact Set.eq_univ_iff_forall

/-- Equality in the actual sheaf identifies the full representing opens without a section. -/
theorem finiteTypeRelativeClassOpen_fppf_eq (T : Over (Spec (.of R)))
    (a b : RelativePic (Limits.pullback.snd f T.hom))
    (hab : relativeFppfClass f T a = relativeFppfClass f T b) :
    finiteTypeRelativeClassOpen f T a = finiteTypeRelativeClassOpen f T b := by
  obtain ⟨𝒰, h𝒰⟩ := relativeFppfClass_eq_exists_cover f T a b hab
  ext t
  let V : T.left.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  obtain ⟨i, u, rfl⟩ := V.exists_eq t
  have h := congrArg (finiteTypeRelativeClassOpen f (relativeCoverMember T 𝒰 i)) (h𝒰 i)
  rw [finiteTypeRelativeClassOpen_map, finiteTypeRelativeClassOpen_map] at h
  exact SetLike.ext_iff.mp h u

end FLT.Mazur.CartierAbel
