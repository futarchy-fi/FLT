/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeIso

/-!
# Recovering group compatibility from the whole action

An equivariant map preserving the actual smooth inclusion preserves multiplication.
The group law then forces preservation of the identity, so compatible geometric
isomorphisms already give an isomorphism of generalized elliptic curves.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
variable {S : Scheme} {E F : GeneralizedEllipticCurve S}

/-- The full action and smooth inclusion determine the group homomorphism condition. -/
theorem isMonHom_of_equivariant (c : E.curve ⟶ F.curve) (g : E.group ⟶ F.group)
    (hi : E.inclusion ≫ c = g ≫ F.inclusion)
    (ha : E.act ≫ c = (g ⊗ₘ c) ≫ F.act) : IsMonHom g := by
  have : Mono F.inclusion := by
    dsimp [inclusion, curveSmoothInclusion]
    infer_instance
  have hm : μ[E.group] ≫ g = (g ⊗ₘ g) ≫ μ[F.group] := by
    apply (cancel_mono F.inclusion).mp
    calc
      (μ[E.group] ≫ g) ≫ F.inclusion =
          E.group ◁ E.inclusion ≫ E.act ≫ c := by
        rw [← Category.assoc, E.action_inclusion]
        simp only [Category.assoc, hi]
      _ = (g ⊗ₘ (E.inclusion ≫ c)) ≫ F.act := by
        rw [ha, ← Category.assoc]
        simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
      _ = (g ⊗ₘ g) ≫ F.group ◁ F.inclusion ≫ F.act := by
        rw [hi, ← Category.assoc]
        simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      _ = ((g ⊗ₘ g) ≫ μ[F.group]) ≫ F.inclusion := by
        rw [F.action_inclusion, Category.assoc]
  have hp (a b : 𝟙_ (Over S) ⟶ E.group) :
      (a * b) ≫ g = (a ≫ g) * (b ≫ g) := by
    simp only [CategoryTheory.Hom.mul_def, Category.assoc, hm, lift_map_assoc]
  refine ⟨?_, hm⟩
  have he : (1 : 𝟙_ (Over S) ⟶ E.group) ≫ g = 1 := by
    apply mul_left_cancel (a := (1 : 𝟙_ (Over S) ⟶ E.group) ≫ g)
    simpa only [_root_.one_mul, _root_.mul_one] using (hp 1 1).symm
  simpa only [CategoryTheory.Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S)))
    (𝟙 _), Category.id_comp] using he

/-- Whole-action comparisons preserving the smooth inclusions lift to full DR isomorphisms. -/
def equivariantIso (c : E.curve ≅ F.curve) (g : E.group ≅ F.group)
    (hi : E.inclusion ≫ c.hom = g.hom ≫ F.inclusion)
    (ha : E.act ≫ c.hom = (g.hom ⊗ₘ c.hom) ≫ F.act) : E ≅ F := by
  let _ := isMonHom_of_equivariant c.hom g.hom hi ha
  exact isoMk c g hi ha

end FLT.Mazur.GeneralizedEllipticCurve
