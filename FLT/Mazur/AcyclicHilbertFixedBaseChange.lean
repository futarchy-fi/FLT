/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicDegreeFixedBaseChange
public import FLT.Mazur.AcyclicHilbertDivisorRepresentation
public import FLT.Mazur.AmpleAffinePullback

/-!
# Actual acyclic Hilbert schemes under coefficient base change

The natural full-divisor comparison identifies the representing schemes.
Thus the original Hilbert scheme pulled to the new coefficient spectrum is
isomorphic to the Hilbert scheme constructed from the base-changed curve.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
local notation "q" => Limits.pullback.snd f a

local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance

include hL in
omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f] in
/-- The original ample line remains ample on the actual coefficient-base-changed curve. -/
theorem fixedBaseAmple :
    AmpleLineBundle ((Scheme.Modules.pullback (Limits.pullback.fst f a)).obj L) := by
  let _ : IsAffineHom (Limits.pullback.fst f a) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact hL.pullback_affine _

/-- The full divisor functors identify the two actual Hilbert representables. -/
def acyclicHilbertFixedBasePresheafIso :
    yoneda.obj ((Over.pullback a).obj (acyclicHilbertTest f d)) ≅
      yoneda.obj (acyclicHilbertTest q d) :=
  (Over.mapPullbackAdj a).compYonedaIso.app (acyclicHilbertTest f d) ≪≫
    Functor.isoWhiskerLeft (Over.map a).op (acyclicHilbertDivisorIso f d hL) ≪≫
    acyclicDegreeFixedBaseIso f a d ≪≫
    (acyclicHilbertDivisorIso q d (fixedBaseAmple f a hL)).symm

/-- The original acyclic Hilbert scheme commutes with actual coefficient base change. -/
def acyclicHilbertFixedBaseIso :
    (Over.pullback a).obj (acyclicHilbertTest f d) ≅ acyclicHilbertTest q d :=
  Yoneda.fullyFaithful.preimageIso (acyclicHilbertFixedBasePresheafIso f a hL d)

/-- The scheme comparison respects the actual structural map to the new coefficient spectrum. -/
@[reassoc]
theorem acyclicHilbertFixedBaseIso_over :
    (acyclicHilbertFixedBaseIso f a hL d).hom.left ≫ (acyclicHilbertTest q d).hom =
      ((Over.pullback a).obj (acyclicHilbertTest f d)).hom :=
  Over.w _

end FLT.Mazur.HilbertChart
