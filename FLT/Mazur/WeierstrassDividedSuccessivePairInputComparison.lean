/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPairSpectrum

/-!
# Comparing complete divided-pair inputs by their two projections

These schematic identities compare full morphisms, including over nonreduced
coefficient rings. The tensor pair retains both own-depth contractions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R} {k l : ℕ}
  (d : Data W π k) (e : Data W π l)

/-- Equality of both divided inputs determines the entire pair morphism. -/
theorem unequalPairSpec_hom_ext {T : Scheme.{u}}
    (f g : T ⟶ Spec (.of (UnequalPairRing d e)))
    (h₁ : f ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom))
    (h₂ : f ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom)) : f = g := by
  apply (cancel_mono (unequalPairSpecIso d e).inv).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, unequalPairSpecIso_fst] using h₁
  · simpa only [Category.assoc, unequalPairSpecIso_snd] using h₂

variable [IsDomain R] (hπ : π ≠ 0)
  (d' : Data W π (k + 1)) (e' : Data W π (l + 1))
  (S : Type u) [CommRing S] [Algebra R S]
local notation "input" =>
  Spec.map (CommRingCat.ofHom (successiveTensorPairInput hπ d d' e e' S).toRingHom)

/-- The first scheme projection is the original first tensor contraction. -/
@[reassoc] theorem successiveTensorPairInput_spec_left :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) =
      Spec.map (CommRingCat.ofHom (successiveTensorPairLeft d' e' S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (successiveTensorInput hπ d d' S).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (successiveTensorPairInput_left hπ d d' e e' S)

/-- The second scheme projection keeps the deeper factor's own contraction. -/
@[reassoc] theorem successiveTensorPairInput_spec_right :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom) =
      Spec.map (CommRingCat.ofHom (successiveTensorPairRight d' e' S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (successiveTensorInput hπ e e' S).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (successiveTensorPairInput_right hπ d d' e e' S)

end FLT.Mazur.WeierstrassDividedDepth
