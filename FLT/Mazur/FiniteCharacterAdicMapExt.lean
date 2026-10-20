/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCharacterAdicElements
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Detecting affine morphisms by all character coefficient reductions

Separatedness of the original complete coefficient ring detects maps from
its character spectrum to any affine spectrum. The character group need not
be finite for this equality criterion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteCharacterAdicElements

variable {R G C : Type} [CommRing R] [AddCommMonoid G] [CommRing C]
  (I : Ideal R) [IsAdicComplete I R]

/-- All positive-order reductions detect the full coordinate homomorphism. -/
theorem ringHom_ext {f g : C →+* AddMonoidAlgebra R G}
    (h : ∀ m, (reduction I m).comp f = (reduction I m).comp g) : f = g := by
  apply RingHom.ext
  intro c
  exact reduction_ext I (fun m => RingHom.congr_fun (h m) c)

/-- The original adic character thickenings detect morphisms to an affine spectrum. -/
theorem specMap_ext
    {f g : Spec (.of (AddMonoidAlgebra R G)) ⟶ Spec (.of C)}
    (h : ∀ m, Spec.map (CommRingCat.ofHom (reduction (G := G) I m)) ≫ f =
      Spec.map (CommRingCat.ofHom (reduction (G := G) I m)) ≫ g) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  apply CommRingCat.hom_ext
  apply ringHom_ext I
  intro m
  have hm := h m
  rw [← Spec.map_preimage f, ← Spec.map_preimage g, ← Spec.map_comp,
    ← Spec.map_comp] at hm
  exact congrArg (fun k => k.hom) (Spec.map_injective hm)

end FLT.Mazur.FiniteCharacterAdicElements
