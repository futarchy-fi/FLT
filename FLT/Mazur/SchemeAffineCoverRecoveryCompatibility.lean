/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonSectionSquareComparison
public import FLT.Mazur.SchemeAffineCoverTestOriginalMap

/-!
# Compatibility of covering recovery on affine source tests

Two affine lifts with the same map to the original source scheme give the
same normalized recovery map. The proof uses the constructed common cover,
its section, and the original descent datum's diagonal identity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison SheafPullbackMapNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
namespace Chart
variable (C : Chart p)

/-- A ring-coordinate square gives the corresponding equality of spectrum maps. -/
lemma spec_square_of_ring_square {A : CommRingCat.{u}}
    (f : C.baseRing ⟶ A) (b : C.coverRing ⟶ A) (hb : C.ringMap ≫ b = f) :
    Spec.map b ≫ Spec.map C.ringMap = Spec.map f :=
  (Spec.map_comp _ _).symm.trans (congrArg Spec.map hb)

/-- An affine covering lift retains its prescribed original base map. -/
lemma cover_spec_over {A : CommRingCat.{u}}
    (f : C.baseRing ⟶ A) (b : C.coverRing ⟶ A) (hb : C.ringMap ≫ b = f) :
    (Spec.map b ≫ C.cover) ≫ p = Spec.map f ≫ C.base := by
  rw [Category.assoc, ← C.square, ← Category.assoc, C.spec_square_of_ring_square f b hb]

end Chart

variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued chartTestRecoveryIso coverRecoveryIso

/-- Equal original source maps give equal normalized covering recovery maps. -/
lemma coverRecoveryIso_affine_compatible_of_square (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base)
    (hs : Spec.map b ≫ (C i).cover = Spec.map c ≫ (C j).cover)
    (ha : Spec.map b ≫ Spec.map (C i).ringMap = Spec.map f)
    (hg : Spec.map c ≫ Spec.map (C j).ringMap = Spec.map g)
    (hz : (Spec.map b ≫ (C i).cover) ≫ p = Spec.map f ≫ (C i).base) :
    normalize (Spec.map b) (C i).cover (C i).cover
        (Spec.map b ≫ (C i).cover) (Spec.map b ≫ (C i).cover) rfl rfl
        (coverRecoveryIso C D i).hom =
      normalize (Spec.map c) (C j).cover (C j).cover
        (Spec.map b ≫ (C i).cover) (Spec.map b ≫ (C i).cover) hs.symm hs.symm
        (coverRecoveryIso C D j).hom := by
  have hl := coverRecoveryIso_test_originalMap C D i f b ha _ _ rfl hz rfl
  have hr := coverRecoveryIso_test_originalMap C D j g c hg _ _ hs.symm hz w.symm
  exact hl.trans ((congrArg ((comparison (Spec.map b ≫ (C i).cover) p
    (Spec.map f ≫ (C i).base) hz).hom.app (openGlued C D) ≫ ·)
      (chartTestRecoveryIso_commonSection_originalMaps_of_square
        C D i j f g b c hb hc w hs ha hg)).trans
        hr.symm)

/-- Equal original source maps give equal normalized covering recovery maps. -/
lemma coverRecoveryIso_affine_compatible (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base)
    (hs : Spec.map b ≫ (C i).cover = Spec.map c ≫ (C j).cover) :
    normalize (Spec.map b) (C i).cover (C i).cover
        (Spec.map b ≫ (C i).cover) (Spec.map b ≫ (C i).cover) rfl rfl
        (coverRecoveryIso C D i).hom =
      normalize (Spec.map c) (C j).cover (C j).cover
        (Spec.map b ≫ (C i).cover) (Spec.map b ≫ (C i).cover) hs.symm hs.symm
        (coverRecoveryIso C D j).hom := by
  exact coverRecoveryIso_affine_compatible_of_square C D i j f g b c hb hc w hs
    ((C i).spec_square_of_ring_square f b hb) ((C j).spec_square_of_ring_square g c hc)
    ((C i).cover_spec_over f b hb)

/-- Only equality of the original source maps is needed for affine covering recovery. -/
lemma coverRecoveryIso_affine_source_compatible (i j : ι) {A : CommRingCat.{u}}
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hs : Spec.map b ≫ (C i).cover = Spec.map c ≫ (C j).cover) :
    normalize (Spec.map b) (C i).cover (C i).cover
        (Spec.map b ≫ (C i).cover) (Spec.map b ≫ (C i).cover) rfl rfl
        (coverRecoveryIso C D i).hom =
      normalize (Spec.map c) (C j).cover (C j).cover
        (Spec.map b ≫ (C i).cover) (Spec.map b ≫ (C i).cover) hs.symm hs.symm
        (coverRecoveryIso C D j).hom := by
  apply coverRecoveryIso_affine_compatible C D i j
    ((C i).ringMap ≫ b) ((C j).ringMap ≫ c) b c rfl rfl _ hs
  simpa only [Spec.map_comp, Category.assoc, Chart.square] using congrArg (· ≫ p) hs

/-- Affine tests may be supplied as scheme maps with an independently named source path. -/
lemma coverRecoveryIso_affine_test_compatible (i j : ι) {A : CommRingCat.{u}}
    (b : Spec A ⟶ Spec (C i).coverRing) (c : Spec A ⟶ Spec (C j).coverRing)
    (d : Spec A ⟶ Y) (hb : b ≫ (C i).cover = d) (hc : c ≫ (C j).cover = d) :
    normalize b (C i).cover (C i).cover d d hb hb (coverRecoveryIso C D i).hom =
      normalize c (C j).cover (C j).cover d d hc hc (coverRecoveryIso C D j).hom := by
  obtain ⟨b, rfl⟩ : ∃ β : (C i).coverRing ⟶ A, Spec.map β = b :=
    ⟨Spec.preimage b, Spec.map_preimage b⟩
  obtain ⟨c, rfl⟩ : ∃ γ : (C j).coverRing ⟶ A, Spec.map γ = c :=
    ⟨Spec.preimage c, Spec.map_preimage c⟩
  subst d
  exact coverRecoveryIso_affine_source_compatible C D i j b c hc.symm

end FLT.Mazur.SchemeAffineDescent
