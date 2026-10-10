/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedCoverLimitDescent
public import FLT.Mazur.ProperImmersedCover

/-!
# Properness descends when an immersed proper cover is available

The fixed proper cover and its ambient proper scheme reduce eventual
properness to global closed-immersion descent. All structure maps keep
the same base, and no finite-presentation assumption is made on the limit.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (g : i ⟶ j), IsClosedImmersion (D.map g)]

include hc in
/-- A fixed immersed proper cover descends properness from a closed inverse limit. -/
theorem exists_isProper_of_immersed_cover {X Z P S : Scheme.{u}}
    [QuasiSeparatedSpace Z] [CompactSpace P]
    (t : D ⟶ (Functor.const I).obj X) [∀ i, IsClosedImmersion (t.app i)]
    (b : c.pt ⟶ X) [IsClosedImmersion b] (hb : ∀ i, c.π.app i ≫ t.app i = b)
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [IsProper (b ≫ f)]
    (p : P ⟶ S) [IsProper p] (π : Z ⟶ X) [IsProper π] [Surjective π]
    (h : Z ⟶ P) [IsImmersion h] [QuasiCompact h] (w : h ≫ p = π ≫ f) :
    ∃ i, IsProper (t.app i ≫ f) := by
  have ww (T : Scheme.{u}) (r : T ⟶ X) :
      (pullback.fst π r ≫ h) ≫ p = pullback.snd π r ≫ (r ≫ f) := by
    rw [Category.assoc, w, ← Category.assoc, pullback.condition, Category.assoc]
  let _ : IsProper ((pullback.fst π b ≫ h) ≫ p) :=
    (ww _ b).symm ▸ inferInstanceAs (IsProper (pullback.snd π b ≫ (b ≫ f)))
  let _ : IsProper (pullback.fst π b ≫ h) := IsProper.of_comp _ p
  have hh : IsClosedImmersion (pullback.fst π b ≫ h) :=
    IsClosedImmersion.of_isPreimmersion _
      (pullback.fst π b ≫ h).isClosedMap.isClosed_range
  obtain ⟨i, hi⟩ := exists_isClosedImmersion_cover_map D c hc t b hb π h hh
  let r : D.obj i ⟶ X := t.app i
  let _ : IsClosedImmersion r := inferInstanceAs (IsClosedImmersion (t.app i))
  exact ⟨i, (isProper_iff_isClosedImmersion_of_cover (r ≫ f) p
    (pullback.snd π r) (pullback.fst π r ≫ h) (ww _ r)).mpr hi⟩

end FLT.Mazur.Approximation
