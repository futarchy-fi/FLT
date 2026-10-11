/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Completing conormal chain maps and their explicit homotopies

Maps of extensions of the same algebra give maps of completed conormal
complexes. The difference homotopy survives completion in both degrees,
without requiring the two presentations to have equal ranks.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicExtensionHomotopy

open Algebra.Extension

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) {P Q : Algebra.Extension R A}

/-- The completed degree-one map of an actual extension morphism. -/
def conormalMap (f : P.Hom Q) := AdicCompletion.map I (Cotangent.map f)

/-- The completed degree-zero map of an actual extension morphism. -/
def spaceMap (f : P.Hom Q) := AdicCompletion.map I (CotangentSpace.map f)

/-- The completed difference of two lifts is the chain homotopy. -/
def homotopy (f g : P.Hom Q) := AdicCompletion.map I (f.sub g)

/-- Completion retains the original commuting square of conormal differentials. -/
theorem chainMap (f : P.Hom Q) :
    (spaceMap I f).comp (AdicCompletion.map I P.cotangentComplex) =
      (AdicCompletion.map I Q.cotangentComplex).comp (conormalMap I f) := by
  unfold spaceMap conormalMap
  rw [AdicCompletion.map_comp, AdicCompletion.map_comp]
  congr 1
  ext x
  exact CotangentSpace.map_cotangentComplex f x

/-- In degree one the difference factors through the original completed differential. -/
theorem conormalMap_sub (f g : P.Hom Q) :
    conormalMap I f - conormalMap I g =
      (homotopy I f g).comp (AdicCompletion.map I P.cotangentComplex) := by
  unfold conormalMap homotopy
  rw [← map_sub, Cotangent.map_sub_map, AdicCompletion.map_comp]

/-- In degree zero the difference factors through the target completed differential. -/
theorem spaceMap_sub (f g : P.Hom Q) :
    spaceMap I f - spaceMap I g =
      (AdicCompletion.map I Q.cotangentComplex).comp (homotopy I f g) := by
  unfold spaceMap homotopy
  rw [← map_sub, CotangentSpace.map_sub_map, AdicCompletion.map_comp]
  rfl

/-- Completing the identity lift gives the identity on conormal modules. -/
@[simp] theorem conormalMap_id : conormalMap I (Hom.id P) = LinearMap.id := by
  simp [conormalMap]

/-- Completing the identity lift gives the identity on cotangent spaces. -/
@[simp] theorem spaceMap_id : spaceMap I (Hom.id P) = LinearMap.id := by
  simp [spaceMap]

variable {T : Algebra.Extension R A}

/-- The degree-one chain map respects composition of actual lifts. -/
theorem conormalMap_comp (f : P.Hom Q) (g : Q.Hom T) :
    conormalMap I (g.comp f) = (conormalMap I g).comp (conormalMap I f) := by
  unfold conormalMap
  rw [Cotangent.map_comp, AdicCompletion.map_comp]
  rfl

/-- The degree-zero chain map respects composition of actual lifts. -/
theorem spaceMap_comp (f : P.Hom Q) (g : Q.Hom T) :
    spaceMap I (g.comp f) = (spaceMap I g).comp (spaceMap I f) := by
  unfold spaceMap
  rw [CotangentSpace.map_comp, AdicCompletion.map_comp]
  rfl

end FLT.Mazur.AdicExtensionHomotopy
