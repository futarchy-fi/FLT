/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalBoundaryCoefficients

/-!
# Exact boundary ideals contain differences between distinct core lifts

Two independently chosen full boundary lifts agree after restriction to the
entire pulled boundary of any common affine test. Their difference therefore
belongs to the original boundary ideal, not just its radical. This identifies
the homogeneous overlap error without asserting that it vanishes ambiently.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IdealSheafClosedTransitions
set_option backward.isDefEq.respectTransparency false
variable {A X Y T : Scheme.{0}}

/-- Independent lifts of one boundary section differ in its full pulled ideal. -/
theorem common_boundary_difference_mem [IsAffine T]
    (J : A.IdealSheafData) (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (f : X ⟶ A) (g : Y ⟶ A) (hI : J.comap f = I) (hK : J.comap g = K)
    (a : T ⟶ X) (b : T ⟶ Y) (hab : a ≫ f = b ≫ g)
    (s : Γ(X, ⊤)) (t : Γ(Y, ⊤)) (v : Γ(J.subscheme, ⊤))
    (hs : I.subschemeι.appTop s = (map I J f hI).appTop v)
    (ht : K.subschemeι.appTop t = (map K J g hK).appTop v) :
    a.appTop s - b.appTop t ∈ (J.comap (a ≫ f)).ideal ⟨⊤, isAffineOpen_top T⟩ := by
  let L := J.comap (a ≫ f)
  have hLI : I.comap a = L := by
    dsimp only [L]
    rw [Scheme.IdealSheafData.comap_comp, hI]
  have hLK : K.comap b = L := by
    dsimp only [L]
    rw [hab, Scheme.IdealSheafData.comap_comp, hK]
  have he : map L I a hLI ≫ map I J f hI = map L K b hLK ≫ map K J g hK := by
    apply (cancel_mono J.subschemeι).mp
    simp only [Category.assoc, map_inclusion, map_inclusion_assoc]
    rw [hab]
  change a.appTop s - b.appTop t ∈ L.ideal ⟨⊤, isAffineOpen_top T⟩
  rw [← L.ker_subschemeι_app ⟨⊤, isAffineOpen_top T⟩]
  change L.subschemeι.appTop (a.appTop s - b.appTop t) = 0
  rw [map_sub, section_square L I a hLI, section_square L K b hLK, hs, ht]
  change (map L I a hLI ≫ map I J f hI).appTop v -
    (map L K b hLK ≫ map K J g hK).appTop v = 0
  rw [he, sub_self]

end FLT.Mazur.IdealSheafClosedTransitions

namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A T : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance overlapBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance overlapBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance overlapBoundaryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n k : ℕ) (a a' : Γ(A, ⊤))
  (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (ha' : A.basicOpen a' ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData)
local notation "C" => rankStageCore e n a ha k
local notation "C'" => rankStageCore e n a' ha' k
local notation "f" => rankStageCoreOriginalMap e n a ha k
local notation "g" => rankStageCoreOriginalMap e n a' ha' k
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J k
local notation "I'" => rankStageCoreBoundaryIdeal e n a' ha' J k
attribute [local irreducible] rankStageCore rankStageCoreBoundaryIdeal

/-- Distinct core choices have an exact homogeneous boundary error on every affine overlap test. -/
theorem rankStage_distinct_core_boundary_difference [IsAffine T]
    (u : T ⟶ (C).toScheme) (u' : T ⟶ (C').toScheme) (hu : u ≫ f = u' ≫ g)
    (v : rankStageCoreInvariants e n a ha k) (v' : rankStageCoreInvariants e n a' ha' k)
    (t : Γ(J.subscheme, ⊤))
    (hv : (I).subschemeι.appTop v.val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t)
    (hv' : (I').subschemeι.appTop v'.val =
      (rankStageCoreOriginalBoundaryMap e n a' ha' J k).appTop t) :
    u.appTop v.val - u'.appTop v'.val ∈ (J.comap (u ≫ f)).ideal ⟨⊤, isAffineOpen_top T⟩ := by
  exact IdealSheafClosedTransitions.common_boundary_difference_mem J I I' f g
    (rankStageCoreOriginalMap_ideal e n a ha J k)
    (rankStageCoreOriginalMap_ideal e n a' ha' J k) u u' hu v.val v'.val t hv hv'

end FLT.Mazur.EquivalenceRelationOrderedFrames
