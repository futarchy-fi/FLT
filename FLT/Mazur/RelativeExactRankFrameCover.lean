/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameTestSplitting

/-!
# Actual splitting covers of schemes supported on exact rank strata

Pulling the original frame scheme back gives an etale surjection over every
scheme supported on an exact rank piece. Its tautological frame splits the
entire original source, preserving the scheme structure of the supplied base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (n : ℕ) {B : Scheme} (b : B ⟶ S)

/-- The actual original frame scheme pulled back to the supplied coefficient scheme. -/
def rankFrameCover : Scheme := pullback (distinctScheme E (Fin n)).hom b

/-- The cover projection retains the full coefficient scheme. -/
def rankFrameProjection : rankFrameCover E n b ⟶ B :=
  pullback.snd (distinctScheme E (Fin n)).hom b

instance rankFrameProjection_etale : Etale (rankFrameProjection E n b) :=
  inferInstanceAs (Etale (pullback.snd (distinctScheme E (Fin n)).hom b))

/-- Its tautological original frame, without any reduction of the base. -/
def rankCoverFrame :
    Over.mk (rankFrameProjection E n b ≫ b) ⟶ distinctScheme E (Fin n) :=
  Over.homMk (pullback.fst (distinctScheme E (Fin n)).hom b) pullback.condition

omit [QuasiCompact E.hom] in
/-- Every coefficient point on the exact rank stratum has an actual frame-cover lift. -/
theorem rankFrameProjection_surjective (hb : Set.range b ⊆ exactRank E n) :
    Function.Surjective (rankFrameProjection E n b) := by
  intro x
  have hx : x ∈ Set.range (pullback.snd (distinctScheme E (Fin n)).hom b) := by
    rw [Scheme.Pullback.range_snd]
    exact (hb (Set.mem_range_self x)).1
  exact hx

/-- The entire original source splits after this constructed etale cover. -/
def rankFrameCoverIso (hb : Set.range b ⊆ exactRank E n) :
    (∐ fun _ : Fin n ↦ rankFrameCover E n b) ≅
      pullback E.hom (rankFrameProjection E n b ≫ b) :=
  rankAtMostTestIso E n (rankCoverFrame E n b) (by
    rintro _ ⟨x, rfl⟩
    exact (hb (Set.mem_range_self (rankFrameProjection E n b x))).2)

/-- Every split component retains its original source coordinate as a scheme morphism. -/
@[reassoc] theorem rankFrameCoverIso_original
    (hb : Set.range b ⊆ exactRank E n) (i : Fin n) :
    Sigma.ι (fun _ : Fin n ↦ rankFrameCover E n b) i ≫
      (rankFrameCoverIso E n b hb).hom ≫
        pullback.fst E.hom (rankFrameProjection E n b ≫ b) =
          (rankCoverFrame E n b ≫ distinctCoordinate E (Fin n) i).left := by
  dsimp only [rankFrameCoverIso, rankAtMostTestIso]
  rw [← Category.assoc, completeTestIso_component, testSection_fst]

end FLT.Mazur.RelativeOrderedTuples
