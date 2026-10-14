/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Comparing two targets through their common unchanged source open

Two morphisms that are isomorphisms over specified opens give an actual
isomorphism between target neighborhoods, by intersecting their source opens.
The construction records the original maps on this common source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CommonUnchangedOpenComparison

variable {X Y Z : Scheme} (f : X ⟶ Y) (g : X ⟶ Z) (U : Y.Opens) (V : Z.Opens)

/-- The common source retains the full inverse images under both original maps. -/
def sourceOpen : X.Opens := f ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V

instance left_open [IsIso (f ∣_ U)] :
    IsOpenImmersion ((sourceOpen f g U V).ι ≫ f) := by
  rw [← Scheme.Hom.resLE_comp_ι f (show sourceOpen f g U V ≤ f ⁻¹ᵁ U from inf_le_left)]
  unfold Scheme.Hom.resLE
  infer_instance

instance right_open [IsIso (g ∣_ V)] :
    IsOpenImmersion ((sourceOpen f g U V).ι ≫ g) := by
  rw [← Scheme.Hom.resLE_comp_ι g (show sourceOpen f g U V ≤ g ⁻¹ᵁ V from inf_le_right)]
  unfold Scheme.Hom.resLE
  infer_instance

variable [IsIso (f ∣_ U)] [IsIso (g ∣_ V)]

/-- The actual target-neighborhood comparison induced by the unchanged common source. -/
def targetIso : ((sourceOpen f g U V).ι ≫ f).opensRange.toScheme ≅
    ((sourceOpen f g U V).ι ≫ g).opensRange.toScheme :=
  ((sourceOpen f g U V).ι ≫ f).isoOpensRange.symm ≪≫
    ((sourceOpen f g U V).ι ≫ g).isoOpensRange

/-- The forward comparison preserves the original right morphism on the common source. -/
@[reassoc] theorem targetIso_hom_inclusion :
    ((sourceOpen f g U V).ι ≫ f).isoOpensRange.hom ≫
      (targetIso f g U V).hom ≫ ((sourceOpen f g U V).ι ≫ g).opensRange.ι =
        (sourceOpen f g U V).ι ≫ g := by
  simp [targetIso]

/-- The inverse comparison preserves the original left morphism on the common source. -/
@[reassoc] theorem targetIso_inv_inclusion :
    ((sourceOpen f g U V).ι ≫ g).isoOpensRange.hom ≫
      (targetIso f g U V).inv ≫ ((sourceOpen f g U V).ι ≫ f).opensRange.ι =
        (sourceOpen f g U V).ι ≫ f := by
  simp [targetIso]

omit [IsIso (f ∣_ U)] [IsIso (g ∣_ V)] in
/-- Any original marking retained by both target opens lies in the common source. -/
theorem marking_range {S : Scheme} (s : S ⟶ X)
    (hf : Set.range (s ≫ f) ⊆ U) (hg : Set.range (s ≫ g) ⊆ V) :
    Set.range s ⊆ sourceOpen f g U V := by
  rintro _ ⟨x, rfl⟩
  exact ⟨hf ⟨x, rfl⟩, hg ⟨x, rfl⟩⟩

end FLT.Mazur.CommonUnchangedOpenComparison
