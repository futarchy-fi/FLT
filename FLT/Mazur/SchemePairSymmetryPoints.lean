/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairBoundaryTransfer

/-!
# Point projections under symmetry of a relative scheme product

Small projection lemmas avoid unfolding the original pair's coordinate rings
when changing the input order of a boundary transfer.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemePairSymmetryPoints
universe u
variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The first input after swapping is exactly the original second input. -/
theorem fst_apply (p : (pullback f g : Scheme)) :
    pullback.fst g f ((pullbackSymmetry f g).hom p) = pullback.snd f g p :=
  congrArg (fun morphism => morphism p) (pullbackSymmetry_hom_comp_fst f g)

/-- The second input after swapping is exactly the original first input. -/
theorem snd_apply (p : (pullback f g : Scheme)) :
    pullback.snd g f ((pullbackSymmetry f g).hom p) = pullback.fst f g p :=
  congrArg (fun morphism => morphism p) (pullbackSymmetry_hom_comp_snd f g)

end FLT.Mazur.SchemePairSymmetryPoints

namespace FLT.Mazur.SchemePairBoundaryTransfer
variable {X X' Y B S : Scheme} (f : X ⟶ S) (f' : X' ⟶ S) (g : Y ⟶ S)
  (a : B ⟶ X) [IsOpenImmersion a] (b : B ⟶ X') (h : a ≫ f = b ≫ f')

/-- The first input of a single boundary transfer belongs to the actual target boundary. -/
theorem transfer_fst_mem_range (p : (domain f g a).toScheme) :
    pullback.fst f' g (transfer f f' g a b h p) ∈ Set.range b := by
  have he := congrArg (fun morphism => morphism p) (transfer_fst f f' g a b h)
  exact ⟨_, he.symm⟩

end FLT.Mazur.SchemePairBoundaryTransfer
