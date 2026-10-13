/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertOriginalTestPullback
public import FLT.Mazur.OrderedHilbertIdentitySheafCoverage
public import FLT.Mazur.RelativeFppfSurjectivityDetection

/-!
# Constructed geometric covers over every original Picard test

The full intersection's unique lifting property transfers the proved sheaf
coverage to its actual test projection. Geometric surjectivity is then detected
on the original fppf site. The resulting etale cover requires no quotient target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertOriginalTestIntersection
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (Z : Over (Spec (.of R))) (sZ : (relativeFppfSheaf f).obj.obj (op Z))

/-- The actual projection to an arbitrary original test covers it in the original fppf site. -/
instance snd_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of R)))
      (uliftYoneda.{1}.map (snd f hL Z sZ)) where
  imageSieve_mem {W} t := by
    have hc : Presheaf.imageSieve (OrderedHilbertIdentityOriginalRelation.sourceMap f hL)
        ((relativeFppfSheaf f).obj.map t.down.op sZ) ∈
          (Scheme.fppfTopology.over (Spec (.of R))) W :=
      Presheaf.IsLocallySurjective.imageSieve_mem _
    apply (Scheme.fppfTopology.over (Spec (.of R))).superset_covering _ hc
    intro V g hg
    obtain ⟨a, ha⟩ := hg
    change (relativeFppfSheaf f).obj.map a.down.op
      (OrderedHilbertIdentityOriginalSection.sourceSection f hL) =
        (relativeFppfSheaf f).obj.map g.op ((relativeFppfSheaf f).obj.map t.down.op sZ) at ha
    have hab : (relativeFppfSheaf f).obj.map a.down.op
        (OrderedHilbertIdentityOriginalSection.sourceSection f hL) =
          (relativeFppfSheaf f).obj.map (g ≫ t.down).op sZ := by
      simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using ha
    obtain ⟨z, hz, _⟩ := lift f hL Z sZ a.down (g ≫ t.down) hab
    exact ⟨ULift.up z, ULift.ext hz.2⟩

/-- This is an actual surjective scheme morphism, with every original component retained. -/
instance snd_surjective : Surjective (snd f hL Z sZ).left :=
  RelativeFppfRepresentedCover.surjective_of_isLocallySurjective (snd f hL Z sZ)

/-- The constructed projection is a single geometric relative fppf cover. -/
theorem snd_covering : Sieve.ofArrows (fun _ : Unit ↦ relation f hL Z sZ)
    (fun _ ↦ snd f hL Z sZ) ∈ (Scheme.fppfTopology.over (Spec (.of R))) Z :=
  RelativeFppfRepresentedCover.covering (snd f hL Z sZ)

/-- The actual scheme projection is effective for arbitrary scheme-valued descent. -/
instance snd_effectiveEpi : EffectiveEpi (snd f hL Z sZ).left := inferInstance

end FLT.Mazur.OrderedHilbertOriginalTestIntersection
