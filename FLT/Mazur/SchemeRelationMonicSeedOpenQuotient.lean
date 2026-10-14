/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedOpen
public import FLT.Mazur.SchemeRelationMonicSeedSelection

/-!
# The quotient on the actual open original source

Transport the constructed quotient through the proved source-open isomorphism.
The result is etale and surjective, with the complete original restricted
relation as its kernel. Its coefficient equation holds as a scheme morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
  [Mono (a ≫ w)] [Mono (pullback.lift p.left q.left h)]
  [Etale p.left] [Etale q.left] [Etale a] [Etale (a ≫ w)]
local notation "W" => sourceOpen (p := p) (q := q) a
local notation "U" => quotientOpen w h a
local notation "i" => Scheme.Opens.ι W
local notation "p'" => SchemeRelationRestriction.fst p.left q.left i
local notation "q'" => SchemeRelationRestriction.snd p.left q.left i

/-- The quotient projection now starts on an actual open of the original source. -/
def openProjection : (W).toScheme ⟶ (U).toScheme :=
  (sourceIso w h a).inv ≫ quotientProjection w h a

@[reassoc]
theorem openProjection_ι : openProjection w h a ≫ (U).ι = i ≫ w := by
  rw [openProjection, Category.assoc, quotientProjection_ι,
    ← Category.assoc, sourceIso_inv_branch]

instance openProjection_etale : Etale (openProjection w h a) :=
  inferInstanceAs (Etale ((sourceIso w h a).inv ≫ quotientProjection w h a))

instance openProjection_surjective : Surjective (openProjection w h a) :=
  inferInstanceAs (Surjective ((sourceIso w h a).inv ≫ quotientProjection w h a))

/-- Every original arrow on the open is coequalized, with both endpoints unrestricted. -/
theorem openProjection_condition : p' ≫ openProjection w h a = q' ≫ openProjection w h a := by
  apply (cancel_mono (U).ι).mp
  simp only [Category.assoc, openProjection_ι]
  rw [← Category.assoc, ← Category.assoc,
    ← SchemeRelationRestriction.arrow_fst, ← SchemeRelationRestriction.arrow_snd]
  rw [Category.assoc, Category.assoc, h]

include e in
/-- The FULL original relation on the actual open is exactly its quotient kernel. -/
theorem openProjection_isPullback : IsPullback p' q' (openProjection w h a)
    (openProjection w h a) := by
  let H := selection_isPullback e w h a i (sourceIso w h a).inv
    (sourceIso_inv_branch w h a)
  have he (c : PullbackCone (openProjection w h a) (openProjection w h a)) :
      c.fst ≫ (i ≫ w) = c.snd ≫ (i ≫ w) := by
    simpa only [Category.assoc, openProjection_ι] using
      congrArg (fun t ↦ t ≫ (U).ι) c.condition
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (openProjection_condition w h a)
    (fun c ↦ H.lift c.fst c.snd (he c))
    (fun c ↦ H.lift_fst c.fst c.snd (he c))
    (fun c ↦ H.lift_snd c.fst c.snd (he c)) ?_)
  intro c z hz₁ hz₂
  apply H.hom_ext
  · exact hz₁.trans (H.lift_fst c.fst c.snd (he c)).symm
  · exact hz₂.trans (H.lift_snd c.fst c.snd (he c)).symm

end FLT.Mazur.SchemeRelationMonicSeedKernel
