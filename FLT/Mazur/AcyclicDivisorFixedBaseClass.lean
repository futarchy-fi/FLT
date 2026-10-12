/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicDivisorFixedBaseChange
public import FLT.Mazur.RelativePicardFppfBaseChange

/-!
# Fixed-base transport retains the Abel class in the original Picard sheaf

The full-divisor comparison and the sheafification comparison agree on actual
relative line classes. This connects the geometric Hilbert comparison to Picard.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The sheaf comparison takes each original relative class to its geometric pullback. -/
theorem relativeFppfBaseChange_class {X S S' : Scheme} (f : X ⟶ S) (a : S' ⟶ S)
    (T : Over S') (c : (relativePresheaf f).obj (op ((Over.map a).obj T))) :
    (relativeFppfBaseChange f a).hom.hom.app (op T)
      (relativeFppfClass f ((Over.map a).obj T) c) =
        relativeFppfClass (Limits.pullback.snd f a) T
          ((relativeBaseChangeValueIso f a T).hom c) := by
  exact congrArg (fun η ↦ η.app (op T) c) (relativeFppfBaseChange_comparison f a)

end FLT.Mazur.SchemePicard

namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] (T : Over (Spec (.of R')))
local notation "q" => Limits.pullback.snd f a
local notation "U" => Functor.obj (Over.map a) T

/-- The transported full divisor has exactly the geometrically pulled-back Abel class. -/
theorem acyclicDivisorFixedBaseChange_class
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f (U).hom)) :
    abel (Limits.pullback.snd q T.hom) (acyclicDivisorFixedBaseChange f a T D).val =
      (relativeBaseChangeValueIso f a T).hom (abel (Limits.pullback.snd f (U).hom) D.val) :=
  finiteTypeAcyclicDivisorCartesianMap_class _ _ _ D

/-- The entire divisor transport commutes with the actual Picard sheaf comparison. -/
theorem acyclicDivisorFixedBaseChange_fppfClass
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f (U).hom)) :
    relativeFppfClass q T
      (abel (Limits.pullback.snd q T.hom) (acyclicDivisorFixedBaseChange f a T D).val) =
        (relativeFppfBaseChange f a).hom.hom.app (op T)
          (relativeFppfClass f (U) (abel (Limits.pullback.snd f (U).hom) D.val)) := by
  rw [acyclicDivisorFixedBaseChange_class, relativeFppfBaseChange_class]

end FLT.Mazur.CartierAbel
