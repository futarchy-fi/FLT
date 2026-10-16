/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationOperations
public import FLT.Mazur.EquivalenceRelationSectionRebase

/-!
# Whole-fiber rebasing for the original Hilbert relation

An arbitrary original relation arrow identifies the entire relation fibers
over its two independent endpoints, as schemes over the unchanged test.
The second endpoint and the original coefficient morphism are preserved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- The actual scheme endpoint maps are jointly monic, before choosing any test base. -/
instance fullRelation_scheme_jointlyMono : JointlyMono₂ (p).left (q).left where
  right_cancellation {T} a b hp hq := by
    let T' : Over (Spec (.of R)) := Over.mk (a ≫ (D).hom)
    let a' : T' ⟶ D := Over.homMk a rfl
    have hb : b ≫ (D).hom = a ≫ (D).hom := by
      rw [← (p).w, ← Category.assoc, ← Category.assoc, hp]
    let b' : T' ⟶ D := Over.homMk b hb
    have h : a' = b' := hom_ext f hL d V c k
      (Over.OverMorphism.ext hp) (Over.OverMorphism.ext hq)
    exact congrArg Over.Hom.left h

/-- The original relation is an internal equivalence relation on the actual schemes. -/
@[irreducible] def fullRelationSchemeEquivalence :
    CategoryTheory.EquivalenceRelation (p).left (q).left := by
  let F := Over.forget (Spec (.of R))
  let _ : JointlyMono₂ (F.map p) (F.map q) :=
    fullRelation_scheme_jointlyMono f hL d V c k
  let er := (equivalence f hL d V c k).toReflexiveRelation.map F
  let es := (equivalence f hL d V c k).toSymmetricRelation.map F
  let et := (equivalence f hL d V c k).toTransitiveRelation.map F
  exact { er, es, et with }

local notation "e" => fullRelationSchemeEquivalence f hL d V c k
variable {T : Scheme} (a : T ⟶ (relation f hL d V c k).left)

/-- A scheme isomorphism of the entire original fibers over independent endpoints. -/
def fullRelationFiberRebase :
    Limits.pullback (p).left (a ≫ (p).left) ≅ Limits.pullback (p).left (a ≫ (q).left) :=
  EquivalenceRelationFiber.rebaseIso (C := Scheme)
    (fullRelationSchemeEquivalence f hL d V c k) a

/-- The rebasing isomorphism is over the original test, not merely over its point set. -/
@[reassoc] theorem fullRelationFiberRebase_test :
    (fullRelationFiberRebase f hL d V c k a).hom ≫
      pullback.snd (p).left (a ≫ (q).left) = pullback.snd (p).left (a ≫ (p).left) :=
  EquivalenceRelationFiber.rebase_snd e a

/-- Every independent original second endpoint is retained by the whole-fiber isomorphism. -/
@[reassoc] theorem fullRelationFiberRebase_second :
    (fullRelationFiberRebase f hL d V c k a).hom ≫
      pullback.fst (p).left (a ≫ (q).left) ≫ (q).left =
        pullback.fst (p).left (a ≫ (p).left) ≫ (q).left := by
  rw [← Category.assoc]
  exact (EquivalenceRelationFiber.rebase_fst_assoc e a _).trans
    (EquivalenceRelationFiber.rebaseArrow_snd e a)

/-- Rebasing preserves the unchanged original coefficient map through the test. -/
@[reassoc] theorem fullRelationFiberRebase_coefficients :
    (fullRelationFiberRebase f hL d V c k a).hom ≫
      pullback.snd (p).left (a ≫ (q).left) ≫ a ≫ (D).hom =
        pullback.snd (p).left (a ≫ (p).left) ≫ a ≫ (D).hom :=
  fullRelationFiberRebase_test_assoc f hL d V c k a _

/-- All original sections are transported bijectively along every original arrow. -/
def fullRelationSectionRebase :
    EquivalenceRelationFiber.Sections («p» := (p).left) (a ≫ (p).left) ≃
      EquivalenceRelationFiber.Sections («p» := (p).left) (a ≫ (q).left) :=
  EquivalenceRelationFiber.sectionRebase e a

end FLT.Mazur.HilbertChart.AffineRestriction
