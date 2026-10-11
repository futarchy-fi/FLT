/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGeometricRankOneOpen

/-!
# The simultaneous acyclic and rank-one open for a varying proper line

First restrict to the constructed global acyclicity open, then take the
intrinsic section-rank-one open there. Its image is an actual open of the
original base, with no global acyclicity assumption on the varying line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve
variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)

local notation "A" => properLineGlobalAcyclicOpen f L hL

/-- The constructed open where the varying line is fiber-acyclic with exactly one section. -/
def properLineAcyclicRankOneOpen : S.Opens :=
  (A).ι ''ᵁ properLineGlobalRankOneOpen (f ∣_ A) ((pullback (f ⁻¹ᵁ A).ι).obj L)
    (hL.pullback _) (properLineGlobalAcyclicOpen_fibers f L hL)

/-- Membership retains both actual positive cohomology vanishing and actual H0 dimension one. -/
theorem mem_properLineAcyclicRankOneOpen (s : S) :
    s ∈ properLineAcyclicRankOneOpen f L hL ↔
      s ∈ properLineGlobalAcyclicOpen f L hL ∧ properLineFiberSectionRank f L s = 1 := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t.property, ?_⟩
    change properLineFiberSectionRank (f ∣_ A) ((pullback (f ⁻¹ᵁ A).ι).obj L) t = 1 at ht
    rwa [properLineFiberSectionRank_baseChange
      (isPullback_morphismRestrict f A).flip L hL] at ht
  · rintro ⟨hs, hr⟩
    refine ⟨⟨s, hs⟩, ?_, rfl⟩
    change properLineFiberSectionRank (f ∣_ A) ((pullback (f ⁻¹ᵁ A).ι).obj L) ⟨s, hs⟩ = 1
    rw [properLineFiberSectionRank_baseChange (isPullback_morphismRestrict f A).flip L hL]
    exact hr

/-- The simultaneous open lies inside the actual acyclicity locus. -/
theorem properLineAcyclicRankOneOpen_le :
    properLineAcyclicRankOneOpen f L hL ≤ properLineGlobalAcyclicOpen f L hL :=
  fun s hs ↦ ((mem_properLineAcyclicRankOneOpen f L hL s).mp hs).1

/-- On any acyclic affine neighborhood this is the original direct-image rank-one open. -/
theorem properLineAcyclicRankOneOpen_eq_affine [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
      Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1))) :
    properLineAcyclicRankOneOpen f L hL = properLineRankOneOpen f L hL hV := by
  ext s
  change s ∈ properLineAcyclicRankOneOpen f L hL ↔
    s ∈ properLineRankOneOpen f L hL hV
  rw [mem_properLineAcyclicRankOneOpen, properLineRankOneOpen_geometric_iff]
  have hs : s ∈ properLineGlobalAcyclicOpen f L hL := fun n ↦
    (residueAlgebraFiber_vanishing_iff f L hL s (n + 1)).mp (hV (S.isoSpec.hom s) n)
  exact and_iff_right hs

/-- Both defining fiber conditions are preserved and detected by arbitrary cartesian base change. -/
theorem properLineAcyclicRankOneOpen_baseChange {P T : Scheme.{0}} [IsLocallyNoetherian T]
    {p : P ⟶ X} {q : P ⟶ T} [IsProper q] [Flat q] {g : T ⟶ S}
    (h : IsPullback p q f g) :
    properLineAcyclicRankOneOpen q ((pullback p).obj L) (hL.pullback p) =
      g ⁻¹ᵁ properLineAcyclicRankOneOpen f L hL := by
  ext t
  change t ∈ properLineAcyclicRankOneOpen _ _ _ ↔
    g t ∈ properLineAcyclicRankOneOpen _ _ _
  rw [mem_properLineAcyclicRankOneOpen, mem_properLineAcyclicRankOneOpen,
    properLineGlobalAcyclicOpen_baseChange f L hL h,
    properLineFiberSectionRank_baseChange h L hL]
  rfl

/-- The simultaneous open represents actual fiber acyclicity and section rank on all test bases. -/
theorem properLineAcyclicRankOneOpen_represents {P T : Scheme.{0}}
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g) :
    (∀ t : T, (∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) ∧
        properLineFiberSectionRank q ((pullback p).obj L) t = 1) ↔
      ∃! a : T ⟶ (properLineAcyclicRankOneOpen f L hL).toScheme,
        a ≫ (properLineAcyclicRankOneOpen f L hL).ι = g := by
  have he (t : T) :
      ((∀ n, Subsingleton
        (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) ∧
          properLineFiberSectionRank q ((pullback p).obj L) t = 1) ↔
        g t ∈ properLineAcyclicRankOneOpen f L hL :=
    (and_congr (forall_congr' fun n ↦ properLine_fiber_vanishing_iff h L hL t (n + 1))
      (congrArg (· = 1) (properLineFiberSectionRank_baseChange h L hL t)).to_iff).trans
        (mem_properLineAcyclicRankOneOpen f L hL (g t)).symm
  rw [show (∀ t : T, _) ↔ ∀ t : T, g t ∈ properLineAcyclicRankOneOpen f L hL from
    forall_congr' he]
  constructor
  · intro ht
    have hr : Set.range g ⊆ Set.range (properLineAcyclicRankOneOpen f L hL).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      exact ht t
    refine ⟨IsOpenImmersion.lift _ g hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    intro b hb
    rw [← cancel_mono (properLineAcyclicRankOneOpen f L hL).ι, hb,
      IsOpenImmersion.lift_fac]
  · rintro ⟨a, ha, _⟩ t
    rw [← ha]
    exact (a t).property

end FLT.Mazur.LineSectionBaseChange
