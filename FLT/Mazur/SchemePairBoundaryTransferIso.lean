/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairBoundaryTransfer

/-!
# Full pair boundary domains are isomorphic under chart transition

When both boundary projections are open immersions, changing the first
input chart gives an isomorphism of the entire corresponding pair opens.
The inverse uses the original boundary in the opposite direction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemePairBoundaryTransfer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X X' Y B S : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S) (g : Y ⟶ S)
  (a : B ⟶ X) [IsOpenImmersion a] (b : B ⟶ X') [IsOpenImmersion b]
  (h : a ≫ f = b ≫ f')
local notation "O" => domain f g a
local notation "O'" => domain f' g b
local notation "tr" => transfer f f' g a b h

/-- The entire transferred pair lies in the opposite boundary domain. -/
theorem transfer_mem_domain (p : (O).toScheme) : tr p ∈ O' := by
  change pullback.fst f' g (tr p) ∈ Set.range b
  refine ⟨boundaryInput f g a p, ?_⟩
  exact (congrArg (fun k => k p) (transfer_fst f f' g a b h)).symm

/-- The whole transfer factors through the full opposite pair domain. -/
def toDomain : (O).toScheme ⟶ (O').toScheme :=
  IsOpenImmersion.lift (O').ι tr (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact transfer_mem_domain f f' g a b h p)

/-- The open factorization retains the original transfer map. -/
@[reassoc] theorem toDomain_ι : toDomain f f' g a b h ≫ (O').ι = tr :=
  IsOpenImmersion.lift_fac _ _ _

/-- Both chart presentations use exactly the same boundary-valued input. -/
@[reassoc] theorem toDomain_boundaryInput :
    toDomain f f' g a b h ≫ boundaryInput f' g b = boundaryInput f g a := by
  apply (cancel_mono b).mp
  rw [Category.assoc, boundaryInput_fac, ← Category.assoc, toDomain_ι, transfer_fst]

/-- The full inverse transition returns the original pair domain pointwise and schematically. -/
theorem toDomain_inverse :
    toDomain f f' g a b h ≫ toDomain f' f g b a h.symm = 𝟙 (O).toScheme := by
  apply (cancel_mono (O).ι).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, toDomain_ι_assoc, transfer_fst,
      toDomain_boundaryInput_assoc, boundaryInput_fac, Category.id_comp]
  · simp only [Category.assoc, toDomain_ι_assoc, transfer_snd, Category.id_comp]

/-- The original full pair boundary domains are isomorphic, without a smaller cover. -/
def domainIso : (O).toScheme ≅ (O').toScheme where
  hom := toDomain f f' g a b h
  inv := toDomain f' f g b a h.symm
  hom_inv_id := toDomain_inverse f f' g a b h
  inv_hom_id := toDomain_inverse f' f g b a h.symm

/-- The domain isomorphism keeps the full map to the new chart pair. -/
@[reassoc] theorem domainIso_hom_ι : (domainIso f f' g a b h).hom ≫ (O').ι = tr :=
  toDomain_ι f f' g a b h

/-- The actual transfer into the new relative pair is an open immersion. -/
instance transfer_isOpenImmersion : IsOpenImmersion tr := by
  rw [← domainIso_hom_ι f f' g a b h]
  infer_instance

end FLT.Mazur.SchemePairBoundaryTransfer
