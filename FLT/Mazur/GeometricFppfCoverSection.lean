/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfCover
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Fppf covers of algebraically closed fields have a split member

Joint surjectivity gives a nonempty member. Finite presentation over the
field makes that member Jacobson, so a closed point gives an actual section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeFppfFamily
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Any fppf covering family of an algebraically closed point has a split member. -/
theorem exists_cover_section (C : Scheme.Cover.{u} Scheme.fppfPrecoverage (Spec (.of k))) :
    ∃ (i : C.I₀) (a : Spec (.of k) ⟶ C.X i), a ≫ C.f i = 𝟙 _ := by
  let V : (Spec (.of k)).Cover
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := C
  obtain ⟨i, y, _⟩ := V.exists_eq (IsLocalRing.closedPoint k)
  let _ : LocallyOfFinitePresentation (C.f i) :=
    (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) C i).2
  let _ : JacobsonSpace (C.X i) := LocallyOfFiniteType.jacobsonSpace (C.f i)
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set (C.X i)).Nonempty from ⟨y, Set.mem_univ _⟩)
    isOpen_univ.isLocallyClosed
  exact ⟨i, pointOfClosedPoint (C.f i) z hz, pointOfClosedPoint_comp (C.f i) z hz⟩

/-- The split member also splits as an arrow of the original relative test category. -/
theorem exists_relative_cover_section {S : Scheme.{u}} (g : Spec (.of k) ⟶ S)
    (C : Scheme.Cover.{u} Scheme.fppfPrecoverage (Spec (.of k))) :
    ∃ (i : C.I₀) (b : Over.mk g ⟶ SchemePicard.relativeCoverMember (Over.mk g) C i),
      b ≫ SchemePicard.relativeCoverArrow (Over.mk g) C i = 𝟙 _ := by
  obtain ⟨i, a, ha⟩ := exists_cover_section C
  let b : Over.mk g ⟶ SchemePicard.relativeCoverMember (Over.mk g) C i :=
    Over.homMk a (by
      change a ≫ C.f i ≫ g = g
      rw [← Category.assoc, ha, Category.id_comp])
  exact ⟨i, b, Over.OverMorphism.ext ha⟩

end FLT.Mazur.SchemeFppfFamily
