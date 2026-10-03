/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateScalarGeneratorComparison

/-!
# Covariant scalar Tate maps in degree minus two

Transport the actual map of abelianizations through the canonical scalar
comparison. The generator formula identifies its action on bar classes.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]

/-- The covariant map of integral scalar Tate groups induced by a group homomorphism. -/
def tateScalarMap (f : H →* G) :
    tateCohomology (Rep.trivial ℤ H ℤ) (-2) →+
      tateCohomology (Rep.trivial ℤ G ℤ) (-2) :=
  (tateScalarAbelianizationEquiv G).symm.toAddMonoidHom.comp
    ((Abelianization.map f).toAdditive.comp
      (tateScalarAbelianizationEquiv H).toAddMonoidHom)

/-- The scalar map sends a bar generator to the image group element's bar generator. -/
theorem tateScalarMap_generator (f : H →* G) (h : H) :
    tateScalarMap f (tateScalarGenerator ℤ H h) = tateScalarGenerator ℤ G (f h) := by
  apply (tateScalarAbelianizationEquiv G).injective
  change tateScalarAbelianizationEquiv G
    ((tateScalarAbelianizationEquiv G).symm _ ) = _
  rw [AddEquiv.apply_symm_apply, tateScalarAbelianizationEquiv_generator]
  change Additive.ofMul (Abelianization.map f
    (Additive.toMul (tateScalarAbelianizationEquiv H (tateScalarGenerator ℤ H h)))) = _
  rw [tateScalarAbelianizationEquiv_generator]
  rfl

/-- Scalar maps respect composition on the actual Tate groups. -/
theorem tateScalarMap_comp {J : Type} [Group J] [Fintype J]
    (f : H →* G) (e : J →* H) :
    (tateScalarMap f).comp (tateScalarMap e) = tateScalarMap (f.comp e) := by
  ext x
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective J x
  simp only [AddMonoidHom.comp_apply, tateScalarMap_generator, MonoidHom.comp_apply]

end LocalClassFieldTheory
