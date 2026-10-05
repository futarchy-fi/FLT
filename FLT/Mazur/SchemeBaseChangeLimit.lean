/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Base change of a connected inverse system of schemes

Pulling a fixed scheme back along every base in a connected inverse system
commutes with its limit. The transition and recovery squares are cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type v} [Category I] {S Y : Scheme.{u}}
  {D : I ⥤ Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) (q : Y ⟶ S)

/-- Base changes of a fixed scheme over a diagram of bases. -/
def schemeBaseChangeDiagram : I ⥤ Scheme.{u} where
  obj i := pullback q (t.app i)
  map {i j} f := pullback.map _ _ _ _ (𝟙 Y) (D.map f) (𝟙 S)
    (by simp) (by simp)
  map_id _ := by apply pullback.hom_ext <;> simp
  map_comp _ _ := by apply pullback.hom_ext <;> simp

/-- The structural maps of the base-changed diagram. -/
def schemeBaseChangeProjection : schemeBaseChangeDiagram t q ⟶ D where
  app i := pullback.snd _ _
  naturality _ _ _ := by simp [schemeBaseChangeDiagram]

/-- Every transition is the actual base change of the corresponding base map. -/
theorem schemeBaseChangeDiagram_isPullback {i j : I} (f : i ⟶ j) :
    IsPullback ((schemeBaseChangeDiagram t q).map f) (pullback.snd q (t.app i))
      (pullback.snd q (t.app j)) (D.map f) := by
  apply IsPullback.of_right _ (by simp [schemeBaseChangeDiagram])
    (IsPullback.of_hasPullback q (t.app j))
  simpa [schemeBaseChangeDiagram, ← t.naturality f] using
    (IsPullback.of_hasPullback q (t.app i))

instance [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i j : I} (f : i ⟶ j) : IsAffineHom ((schemeBaseChangeDiagram t q).map f) :=
  MorphismProperty.of_isPullback (schemeBaseChangeDiagram_isPullback t q f).flip
    (inferInstanceAs (IsAffineHom (D.map f)))

variable (c : Cone D) (b : c.pt ⟶ S) (hb : ∀ i, c.π.app i ≫ t.app i = b)

/-- The pullback of the limiting base has a canonical cone to the model diagram. -/
def schemeBaseChangeCone : Cone (schemeBaseChangeDiagram t q) where
  pt := pullback q b
  π.app i := pullback.map _ _ _ _ (𝟙 Y) (c.π.app i) (𝟙 S)
    (by simp) (by simpa using (hb i).symm)
  π.naturality _ _ _ := by
    apply pullback.hom_ext <;> simp [schemeBaseChangeDiagram]

/-- The comparison to each model stage is cartesian over its base projection. -/
theorem schemeBaseChangeCone_isPullback (i : I) :
    IsPullback ((schemeBaseChangeCone t q c b hb).π.app i) (pullback.snd q b)
      (pullback.snd q (t.app i)) (c.π.app i) := by
  apply IsPullback.of_right _ (by simp [schemeBaseChangeCone])
    (IsPullback.of_hasPullback q (t.app i))
  simpa [schemeBaseChangeCone, hb i] using (IsPullback.of_hasPullback q b)

/-- A connected inverse limit commutes with base change of a fixed scheme. -/
def schemeBaseChangeIsLimit [IsConnected I] (hc : IsLimit c) :
    IsLimit (schemeBaseChangeCone t q c b hb) :=
  isLimitOfIsPullbackOfIsConnected (schemeBaseChangeProjection t q) _ _
    { hom := pullback.snd q b
      w i := (schemeBaseChangeCone_isPullback t q c b hb i).w.symm }
    (schemeBaseChangeCone_isPullback t q c b hb) hc

end FLT.Mazur.Approximation
