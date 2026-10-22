/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRankOneTests
public import FLT.Mazur.InvariantIdealEquivalence

/-!
# Exact original boundary arrows with a rank-one endpoint

On a full rank-one test, an original boundary arrow exists exactly when
the two boundary morphisms agree. Reflexivity constructs the arrow in
that case. This is scheme-level equality, with all nilpotents retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local instance onePairOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance onePairOver_etale : Etale (Over.mk p).hom := ‹Etale p›
variable (x y : B ⟶ J.subscheme)
  (hx : Set.range (x ≫ J.subschemeι) ⊆ rankAtMost (Over.mk p) 1)
include e hx

/-- Every full boundary arrow with first rank one has identical boundary endpoints. -/
theorem originalBoundary_rankOne_endpoints_eq
    (d : B ⟶ pullback p J.subschemeι)
    (hd : d ≫ pullback.snd p J.subschemeι = x)
    (hd' : d ≫ InvariantIdealRelation.snd J p q hJ = y) : x = y := by
  have hp : (d ≫ pullback.fst p J.subschemeι) ≫ p = (𝟙 B) ≫ x ≫ J.subschemeι := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hd, Category.id_comp]
  have hq := original_rankOne_arrow_endpoints e (x ≫ J.subschemeι) hx
    (d ≫ pullback.fst p J.subschemeι) (𝟙 B) hp
  apply (cancel_mono J.subschemeι).mp
  calc
    x ≫ J.subschemeι = (d ≫ pullback.fst p J.subschemeι) ≫ q := by
      simpa only [Category.id_comp] using hq.symm
    _ = y ≫ J.subschemeι := by
      rw [Category.assoc, ← InvariantIdealRelation.snd_ι J p q hJ, ← Category.assoc, hd']

/-- Equality constructs an actual unique original arrow on the entire rank-one test. -/
theorem originalBoundary_rankOne_arrow_iff :
    (∃! d : B ⟶ pullback p J.subschemeι,
      d ≫ pullback.snd p J.subschemeι = x ∧
        d ≫ InvariantIdealRelation.snd J p q hJ = y) ↔ x = y := by
  constructor
  · rintro ⟨d, hd, _⟩
    exact originalBoundary_rankOne_endpoints_eq e J hJ x y hx d hd.1 hd.2
  · intro hxy
    let eJ := InvariantIdealRelation.equivalence J hJ e
    let _ : JointlyMono₂ (pullback.snd p J.subschemeι)
        (InvariantIdealRelation.snd J p q hJ) := eJ.toJointlyMono₂
    have hp : (x ≫ eJ.r) ≫ pullback.snd p J.subschemeι = x := by
      rw [Category.assoc, eJ.reflexivity₁, Category.comp_id]
    have hq : (x ≫ eJ.r) ≫ InvariantIdealRelation.snd J p q hJ = y := by
      rw [Category.assoc, eJ.reflexivity₂, Category.comp_id, hxy]
    refine ⟨x ≫ eJ.r, ⟨hp, hq⟩, fun d hd ↦ ?_⟩
    apply JointlyMono₂.right_cancellation (p₁ := pullback.snd p J.subschemeι)
      (p₂ := InvariantIdealRelation.snd J p q hJ)
    · exact hd.1.trans hp.symm
    · exact hd.2.trans hq.symm

end FLT.Mazur.EquivalenceRelationOrderedFrames
