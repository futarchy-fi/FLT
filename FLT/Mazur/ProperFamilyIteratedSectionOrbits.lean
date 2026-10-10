/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyOrbitPullback
public import FLT.Mazur.OriginalTwistIsoRigidity

/-!
# Original twisting-line meaning of iterated geometric section pullback

The unit and composite comparisons preserve the actual original sections.
Their existence follows from geometric orbit laws, and local splitting makes
any section-preserving original twisting-line comparison unique.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open ProperFamilyAtlas FCurve LineSectionBaseChange DualAtlasLineQuotient
open LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.projection
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "N" => Functor.obj (pushforward q) (Functor.obj (pullback p) L)


local notation "R" => RelativeSection q (Functor.obj (pullback p) L) (hL.pullback p)

local notation "π" => projection M hM

open ProperFamilyTests Opposite

variable {A B C : Family f}

/-- The directly pulled identity section differs only by its original twist isomorphism. -/
lemma familySectionMap_id_relation
    (s : RelativeSection A.snd ((pullback A.fst).obj L) (hL.pullback A.fst)) :
    originalTwistIsoRelation A.snd ((pullback A.fst).obj L)
      (familySectionMap L hL hV (𝟙 A) s).val s.val := by
  apply (familyBaseLineSetoid_iff_iso A.square L hL hV _ _).mp
  apply (toFamilyAtlas_eq_iff A.square L hL hV _ _).mp
  rw [familySectionMap_toAtlas]
  exact familyAtlasPrecomp_id L hL hV _

/-- Iterated direct pullback has an original twisting-line comparison to composite pullback. -/
lemma familySectionMap_comp_relation (u : A ⟶ B) (v : B ⟶ C)
    (s : RelativeSection C.snd ((pullback C.fst).obj L) (hL.pullback C.fst)) :
    originalTwistIsoRelation A.snd ((pullback A.fst).obj L)
      (familySectionMap L hL hV u (familySectionMap L hL hV v s)).val
      (familySectionMap L hL hV (u ≫ v) s).val := by
  apply (familyBaseLineSetoid_iff_iso A.square L hL hV _ _).mp
  apply (toFamilyAtlas_eq_iff A.square L hL hV _ _).mp
  rw [familySectionMap_toAtlas, familySectionMap_toAtlas, familySectionMap_toAtlas]
  exact familyAtlasPrecomp_comp L hL hV v.base u.base v.over u.over _

include hV in
/-- Original section-preserving comparisons are unique on every original test family. -/
lemma familyOriginalTwistIso_unique
    (s t : RelativeSection A.snd ((pullback A.fst).obj L) (hL.pullback A.fst))
    (e d : s.val.baseLine.val ≅ t.val.baseLine.val)
    (he : (ModuleSheafTensor.map (𝟙 ((pullback A.fst).obj L))
      ((pullback A.snd).map e.hom)).app ⊤ s.val.section_ = t.val.section_)
    (hd : (ModuleSheafTensor.map (𝟙 ((pullback A.fst).obj L))
      ((pullback A.snd).map d.hom)).app ⊤ s.val.section_ = t.val.section_) : e = d :=
  originalTwistIso_unique A.snd ((pullback A.fst).obj L) s.val t.val
    (familyOriginalSection_locallySplit A.square L hL hV s) e d he hd

end FLT.Mazur.CartierAbel
