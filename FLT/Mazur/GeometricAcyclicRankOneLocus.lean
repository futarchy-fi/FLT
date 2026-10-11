/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricAcyclicRankOne

/-!
# The intrinsic geometric acyclic rank-one locus

The locus is defined on any base by actual fiber cohomology and section
rank. Isomorphisms preserve it, and proper-family base change pulls it
back as a set without Noetherian restrictions on either base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- The points whose actual line fiber is acyclic and has exactly one section. -/
def geometricAcyclicRankOneLocus (L : X.Modules) : Set S :=
  {s | (∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1))) ∧
    properLineFiberSectionRank f L s = 1}

/-- A sheaf isomorphism preserves the entire geometric locus pointwise. -/
theorem geometricAcyclicRankOneLocus_iso {L M : X.Modules} (e : L ≅ M) :
    geometricAcyclicRankOneLocus f L = geometricAcyclicRankOneLocus f M := by
  ext s
  let a := (pullback (f.fiberι s)).mapIso e
  exact and_congr (forall_congr' fun n ↦
    Equiv.subsingleton_congr (moduleHIsoOfIso a (n + 1)).toEquiv)
      (congrArg (· = 1) (fiberSectionRank_eq_of_iso f s a)).to_iff

/-- For proper families the locus commutes with all cartesian changes of base. -/
theorem geometricAcyclicRankOneLocus_baseChange [IsProper f]
    {P T : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
    (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L) :
    geometricAcyclicRankOneLocus q ((pullback p).obj L) =
      g ⁻¹' geometricAcyclicRankOneLocus f L := by
  ext t
  exact and_congr (forall_congr' fun n ↦ properLine_fiber_vanishing_iff h L hL t (n + 1))
    (congrArg (· = 1) (properLineFiberSectionRank_baseChange h L hL t)).to_iff

/-- On a Noetherian original base the constructed open has this exact intrinsic set. -/
theorem geometricAcyclicRankOneLocus_eq_open [IsLocallyNoetherian S] [IsProper f] [Flat f]
    (L : X.Modules) (hL : LocallyFreeRankOne L) :
    geometricAcyclicRankOneLocus f L = (properLineAcyclicRankOneOpen f L hL : Set S) := by
  ext s
  exact (mem_properLineAcyclicRankOneOpen f L hL s).symm

end FLT.Mazur.CartierAbel
