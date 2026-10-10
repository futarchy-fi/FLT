/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineRankOneDetection

/-!
# The rank-one open represents the direct-image line condition

Detection descends from affine neighborhoods of an arbitrary test scheme.
The resulting equivalence is the actual unique factorization through the
constructed open immersion, not a chosen scheme with a representation field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  {P T : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
  (h : IsPullback p q f g)

include h in
/-- The actual direct-image line condition is detected on unrestricted test schemes. -/
theorem properLineBaseChanged_rankOne_iff :
    LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)) ↔
      ∀ t : T, g t ∈ properLineRankOneOpen f L hL hV := by
  refine ⟨fun hN t ↦ ?_, properLineBaseChanged_rankOne f L hL hV h⟩
  obtain ⟨U, hU, ht, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := t) (by trivial)
  let _ : IsAffine U.toScheme := hU
  have hpull := hN.of_iso (properLineArbitraryBaseChangeIso h L hL hV).symm
  have hpull' := (hpull.pullback U.ι).of_iso ((pullbackComp U.ι g).app _)
  let k := (isPullback_morphismRestrict q U).flip.paste_horiz h
  have hN' := hpull'.of_iso (properLineArbitraryBaseChangeIso k L hL hV)
  exact (properLineBaseChanged_rankOne_iff_affine f L hL hV k).mp hN' ⟨t, ht⟩

/-- The unique factorization into the actual open, constructed from the direct-image line. -/
def properLineRankOneLift
    (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L))) :
    T ⟶ (properLineRankOneOpen f L hL hV).toScheme :=
  IsOpenImmersion.lift (properLineRankOneOpen f L hL hV).ι g (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact (properLineBaseChanged_rankOne_iff f L hL hV h).mp hN t)

/-- The lift retains the original test morphism. -/
lemma properLineRankOneLift_fac
    (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L))) :
    properLineRankOneLift f L hL hV h hN ≫ (properLineRankOneOpen f L hL hV).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- Every competing factorization agrees as an actual morphism into the constructed open. -/
lemma properLineRankOneLift_unique
    (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)))
    (a : T ⟶ (properLineRankOneOpen f L hL hV).toScheme)
    (ha : a ≫ (properLineRankOneOpen f L hL hV).ι = g) :
    a = properLineRankOneLift f L hL hV h hN := by
  rw [← cancel_mono (properLineRankOneOpen f L hL hV).ι, ha, properLineRankOneLift_fac]

include h in
/-- The open immersion represents precisely the actual direct-image line condition. -/
theorem properLineRankOneOpen_represents :
    LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)) ↔
      ∃! a : T ⟶ (properLineRankOneOpen f L hL hV).toScheme,
        a ≫ (properLineRankOneOpen f L hL hV).ι = g := by
  refine ⟨fun hN ↦ ⟨properLineRankOneLift f L hL hV h hN,
    properLineRankOneLift_fac f L hL hV h hN,
    properLineRankOneLift_unique f L hL hV h hN⟩, ?_⟩
  rintro ⟨a, ha, _⟩
  apply (properLineBaseChanged_rankOne_iff f L hL hV h).mpr
  intro t
  rw [← ha]
  exact (a t).property

end FLT.Mazur.LineSectionBaseChange
