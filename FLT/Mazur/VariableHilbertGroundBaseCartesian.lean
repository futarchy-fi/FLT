/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertFixedBaseProjection

/-!
# Cartesian Hilbert transport across a changed ground base

The actual Hilbert comparison is Cartesian over the translation map even
when the coefficient extension is not monic. This permits genuine etale
coefficient extensions and retains every scheme-theoretic residue branch.
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

/-- The Hilbert comparison is the actual ground-base pullback projection. -/
theorem acyclicHilbertGroundBase_isPullback :
    IsPullback (acyclicHilbertFixedBaseProjection f a hL d).left
      (acyclicHilbertTest q d).hom (acyclicHilbertTest f d).hom a := by
  let e := (Over.forget _).mapIso (acyclicHilbertFixedBaseIso f a hL d).symm
  apply IsPullback.of_iso_pullback ⟨Over.w _⟩ e
  · rfl
  · exact Over.w (acyclicHilbertFixedBaseIso f a hL d).inv

variable (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V)

/-- Changing both ground base and translation gives an actual Cartesian parameter square. -/
theorem variableHilbertGroundBase_isPullback :
    IsPullback (variableHilbertFixedBaseProjection f a hL d V W t).left
      (variableHilbertBase q d W).left (variableHilbertBase f d V).left t.left := by
  have hn := Over.isPullback_of_binaryFan_isLimit _
    (prodIsProd W (acyclicHilbertTest q d))
  have ho := Over.isPullback_of_binaryFan_isLimit _
    (prodIsProd V (acyclicHilbertTest f d))
  have hc := hn.flip.paste_horiz (acyclicHilbertGroundBase_isPullback f a hL d)
  have hb := congrArg Over.Hom.left
    (variableHilbertFixedBaseProjection_base f a hL d V W t)
  have hh := congrArg Over.Hom.left
    (variableHilbertFixedBaseProjection_hilbert f a hL d V W t)
  simp only [Over.comp_left, Over.map_map_left] at hb hh
  apply IsPullback.of_right (t := ho.flip) (p := hb)
  change IsPullback
    ((variableHilbertFixedBaseProjection f a hL d V W t).left ≫
      (variableHilbertParameter f d V).left)
    (variableHilbertBase q d W).left (acyclicHilbertTest f d).hom (t.left ≫ V.hom)
  rw [hh, Over.w t]
  exact hc

/-- Every base-change-stable property of the translation map survives on Hilbert parameters. -/
theorem variableHilbertGroundBase_property (P : MorphismProperty Scheme)
    [P.IsStableUnderBaseChange] (ht : P t.left) :
    P (variableHilbertFixedBaseProjection f a hL d V W t).left :=
  MorphismProperty.of_isPullback
    (variableHilbertGroundBase_isPullback f a hL d V W t).flip ht

end FLT.Mazur.HilbertChart
