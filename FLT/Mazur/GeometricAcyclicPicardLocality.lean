/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeAcyclicPicardOpen

/-!
# Locality of the geometric acyclic Picard locus

Jointly surjective cartesian families detect the geometric condition. In
particular its relative Picard subfunctor is local for actual fppf covering
families on arbitrary test schemes, with no Noetherian or reducedness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f]

/-- Jointly surjective cartesian tests detect both fiber acyclicity and section rank. -/
theorem geometricAcyclicRankOne_of_jointlySurjective {ι : Type*}
    (P T : ι → Scheme.{0}) (p : ∀ i, P i ⟶ X) (q : ∀ i, P i ⟶ T i)
    (g : ∀ i, T i ⟶ S) (H : ∀ i, IsPullback (p i) (q i) f (g i))
    (hg : ∀ s : S, ∃ i, ∃ t : T i, g i t = s)
    (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : ∀ i, GeometricAcyclicRankOne (q i) ((Scheme.Modules.pullback (p i)).obj L)) :
    GeometricAcyclicRankOne f L := by
  intro s
  obtain ⟨i, t, rfl⟩ := hg s
  exact ⟨fun n ↦ (properLine_fiber_vanishing_iff (H i) L hL t (n + 1)).mp ((hA i t).1 n),
    (properLineFiberSectionRank_baseChange (H i) L hL t).symm.trans (hA i t).2⟩

/-- Membership of an actual relative class in the acyclic locus is local for fppf families. -/
theorem relativeGeometricAcyclicRankOne_fppf_iff (T : Over S)
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.hom) c ↔
      ∀ i, RelativeGeometricAcyclicRankOne
        (Limits.pullback.snd f (relativeCoverMember T 𝒰 i).hom)
        (relativeBaseMap f (relativeCoverArrow T 𝒰 i) c) := by
  constructor
  · intro hc i
    exact relativeGeometricAcyclicRankOne_map _
      (relativeTotalMap_isPullback f (relativeCoverArrow T 𝒰 i)) hc
  · intro hc
    obtain ⟨L, rfl⟩ := relativePic_exists_line (Limits.pullback.snd f T.hom) c
    apply (relativeGeometricAcyclicRankOne_mk _ L.val L.property).mpr
    let V : T.left.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
    apply geometricAcyclicRankOne_of_jointlySurjective (Limits.pullback.snd f T.hom)
      (fun i ↦ Limits.pullback f (relativeCoverMember T 𝒰 i).hom) 𝒰.X
      (fun i ↦ relativeTotalMap f (relativeCoverArrow T 𝒰 i))
      (fun i ↦ Limits.pullback.snd f (relativeCoverMember T 𝒰 i).hom) 𝒰.f
      (fun i ↦ relativeTotalMap_isPullback f (relativeCoverArrow T 𝒰 i))
      (fun t ↦ V.exists_eq t) L.val L.property
    intro i
    exact (relativeGeometricAcyclicRankOne_mk _ _ (L.property.pullback _)).mp (hc i)

end FLT.Mazur.CartierAbel
