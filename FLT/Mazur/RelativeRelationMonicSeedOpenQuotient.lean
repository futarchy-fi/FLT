/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedOpenQuotient
public import FLT.Mazur.RelativeFppfSchemeCover

/-!
# Relative scheme coequalization on the actual original source open

The constructed open-source quotient is a scheme over the original coefficient
base. Every relative scheme morphism coequalizing the full original restricted
relation descends uniquely. This retains structure morphisms, not only points
or a locally ringed-space quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationMonicSeedOpenQuotient
set_option backward.isDefEq.respectTransparency false
variable {S Z : Scheme.{u}} {D A T : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A ⟶ T)
  (h : p.left ≫ w.left = q.left ≫ w.left) (a : Z ⟶ A.left)
  [Etale p.left] [Etale q.left] [Etale a] [Etale (a ≫ w.left)]
  [Mono (a ≫ w.left)] [Mono (pullback.lift p.left q.left h)]
local notation "W" => SchemeRelationMonicSeedKernel.sourceOpen (p := p) (q := q) a
local notation "b" => Scheme.Opens.ι W
local notation "U" => SchemeRelationMonicSeedKernel.quotientOpen w.left h a
local notation "π" => SchemeRelationMonicSeedKernel.openProjection w.left h a
local notation "p'" => SchemeRelationRestriction.fst p.left q.left b
local notation "q'" => SchemeRelationRestriction.snd p.left q.left b

/-- The actual open source retains its actual original coefficient-base morphism. -/
def source : Over S := Over.mk (b ≫ A.hom)

/-- The quotient is an actual open of the coefficient model over the same base. -/
def target : Over S := Over.mk ((U).ι ≫ T.hom)

/-- The etale surjective quotient projection as an actual relative scheme morphism. -/
def projection : source (p := p) (q := q) a ⟶ target w h a := Over.homMk π (by
  change π ≫ (U).ι ≫ T.hom = b ≫ A.hom
  rw [← Category.assoc, SchemeRelationMonicSeedKernel.openProjection_ι,
    Category.assoc, w.w])

instance projection_etale : Etale (projection w h a).left :=
  inferInstanceAs (Etale π)

instance projection_surjective : Surjective (projection w h a).left :=
  inferInstanceAs (Surjective π)

variable {Y : Over S} (t : source (p := p) (q := q) a ⟶ Y)

include e in
/-- The entire original restricted relation constructs the descent compatibility equation. -/
theorem kernel_compatible (ht : p' ≫ t.left = q' ≫ t.left) :
    pullback.fst (projection w h a) (projection w h a) ≫ t =
      pullback.snd (projection w h a) (projection w h a) ≫ t := by
  let H := SchemeRelationMonicSeedKernel.openProjection_isPullback e w.left h a
  let x := (pullback.fst (projection w h a) (projection w h a)).left
  let y := (pullback.snd (projection w h a) (projection w h a)).left
  have hxy : x ≫ π = y ≫ π := congrArg Over.Hom.left pullback.condition
  apply Over.OverMorphism.ext
  change x ≫ t.left = y ≫ t.left
  have he := congrArg (fun g ↦ H.lift x y hxy ≫ g) ht
  simpa only [← Category.assoc, H.lift_fst, H.lift_snd] using he

include e in
/-- Every coequalizing scheme map descends uniquely with its original base map intact. -/
theorem existsUnique_descend (ht : p' ≫ t.left = q' ≫ t.left) :
    ∃! s : target w h a ⟶ Y, projection w h a ≫ s = t :=
  RelativeFppfSchemeCover.existsUnique (projection w h a) t
    (kernel_compatible e w h a t ht)

end FLT.Mazur.RelativeRelationMonicSeedOpenQuotient
