/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairDoubleBoundaryTransfer

/-!
# Both transferred inputs remain in their actual target boundaries

The original explicit boundary factorizations certify membership in the
full target ranges; no new nonvanishing assumption is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemePairDoubleBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X X' Y Y' B C S Z : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S)
  (a : B ⟶ X) [IsOpenImmersion a] (b : B ⟶ X')
  (c : C ⟶ Y) [IsOpenImmersion c] (d : C ⟶ Y')
  (h : a ≫ f = b ≫ f') (k : c ≫ g = d ≫ g')
local notation "D" => domain f g a c
local notation "t" => transfer f f' g g' a b c d h k

/-- The first transferred input belongs to the entire original first target boundary. -/
theorem transfer_fst_mem_range (p : (D).toScheme) :
    pullback.fst f' g' (t p) ∈ Set.range b := by
  have hm := transfer_fst f f' g g' a b c d h k
  rw [SchemePairBoundaryTransfer.transfer_fst] at hm
  have he := congrArg (fun m => m p) hm
  exact ⟨_, he.symm⟩

/-- The second transferred input belongs to the entire original second target boundary. -/
theorem transfer_snd_mem_range (p : (D).toScheme) :
    pullback.snd f' g' (t p) ∈ Set.range d := by
  have he := congrArg (fun m => m p) (transfer_snd f f' g g' a b c d h k)
  exact ⟨_, he.symm⟩

end FLT.Mazur.SchemePairDoubleBoundary
