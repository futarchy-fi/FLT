/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicDivisorFixedBaseClass
public import FLT.Mazur.AcyclicHilbertFixedBaseIdeal
public import FLT.Mazur.AcyclicHilbertPicardTestOverlap

/-!
# The actual Hilbert scheme comparison commutes with the Picard map

The equality follows from full-divisor transport and its Abel class, so it
retains the previously constructed parameter scheme and universal family.
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

/-- The parameter comparison retains the original Picard-sheaf class on every test. -/
theorem acyclicHilbertFixedBaseParameter_picard (T : Over (Spec (.of R')))
    (k : (Over.map a).obj T ⟶ acyclicHilbertTest f d) :
    acyclicHilbertPicardPoint q d (fixedBaseAmple f a hL) T
        (acyclicHilbertFixedBaseParameter f a hL d T k) =
      (relativeFppfBaseChange f a).hom.hom.app (op T)
        (acyclicHilbertPicardPoint f d hL ((Over.map a).obj T) k) := by
  have hd := congrArg Subtype.val (acyclicHilbertFixedBaseParameter_divisor f a hL d T k)
  change acyclicHilbertParameterDivisor q d T _ =
    acyclicDivisorFixedBaseChange f a T (acyclicHilbertParameterDivisor f d _ k) at hd
  change relativeFppfClass q T (abel _ (acyclicHilbertParameterDivisor q d T _).val) = _
  rw [hd]
  exact acyclicDivisorFixedBaseChange_fppfClass f a T _

/-- The actual scheme isomorphism intertwines the two Hilbert Abel maps. -/
theorem acyclicHilbertFixedBaseIso_picard (T : Over (Spec (.of R')))
    (k : T ⟶ (Over.pullback a).obj (acyclicHilbertTest f d)) :
    acyclicHilbertPicardPoint q d (fixedBaseAmple f a hL) T
        (k ≫ (acyclicHilbertFixedBaseIso f a hL d).hom) =
      (relativeFppfBaseChange f a).hom.hom.app (op T)
        (acyclicHilbertPicardPoint f d hL ((Over.map a).obj T)
          (((Over.mapPullbackAdj a).homEquiv T (acyclicHilbertTest f d)).symm k)) := by
  rw [acyclicHilbertFixedBaseIso_point, acyclicHilbertFixedBaseParameter_picard]

/-- The transported parameter satisfies precisely the original class equation. -/
theorem acyclicHilbertFixedBaseParameter_picard_eq_iff (T : Over (Spec (.of R')))
    (k : (Over.map a).obj T ⟶ acyclicHilbertTest f d)
    (s : (relativeFppfSheaf f).obj.obj (op ((Over.map a).obj T))) :
    acyclicHilbertPicardPoint q d (fixedBaseAmple f a hL) T
        (acyclicHilbertFixedBaseParameter f a hL d T k) =
      (relativeFppfBaseChange f a).hom.hom.app (op T) s ↔
        acyclicHilbertPicardPoint f d hL ((Over.map a).obj T) k = s := by
  rw [acyclicHilbertFixedBaseParameter_picard]
  let e := ((sheafToPresheaf _ _).mapIso (relativeFppfBaseChange f a)).app (op T)
  change e.hom _ = e.hom _ ↔ _
  constructor
  · intro h
    have hh := congrArg (fun z ↦ e.inv z) h
    simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply] using hh
  · exact congrArg _

end FLT.Mazur.HilbertChart
