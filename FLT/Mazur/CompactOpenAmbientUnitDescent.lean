/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompactOpenUnitDescent
public import FLT.Mazur.OpenSectionTopComparison

/-!
# Descent of units in ambient section rings

Translate the compact-open unit construction from global sections of open
subschemes to ambient sections, retaining the actual section pullback maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Actual ambient units descend with their restriction and multiplication equations. -/
theorem exists_compactOpen_ambient_units {J : Type v} [SmallCategory J] [FinCategory J]
    (i : I) (O : J → (D.obj i).Opens)
    (hO : ∀ {j k}, (j ⟶ k) → O k ≤ O j)
    (hcompact : ∀ j, IsCompact (O j : Set (D.obj i)))
    (K L : J → Type v) [∀ j, Finite (K j)] [∀ j, Finite (L j)]
    (x : ∀ j, K j → Γ(c.pt, c.π.app i ⁻¹ᵁ O j)ˣ)
    (τ : ∀ {j k}, (j ⟶ k) → K j → K k)
    (hx : ∀ {j k} (f : j ⟶ k) a,
      c.pt.presheaf.map (homOfLE ((c.π.app i).preimage_mono (hO f))).op (x j a) =
        (x k (τ f a) : Γ(c.pt, c.π.app i ⁻¹ᵁ O k)))
    (a b d : ∀ j, L j → K j)
    (hmul : ∀ j l, x j (a j l) * x j (b j l) = x j (d j l)) :
    ∃ (r : Over i) (y : ∀ j, K j → Γ(D.obj r.left, D.map r.hom ⁻¹ᵁ O j)ˣ),
      (∀ j k, Units.map ((c.π.app r.left).appLE _ _
        (by rw [← Scheme.Hom.comp_preimage, c.w])).hom.toMonoidHom (y j k) = x j k) ∧
      (∀ {j k} (f : j ⟶ k) l,
        (D.obj r.left).presheaf.map
          (homOfLE ((D.map r.hom).preimage_mono (hO f))).op (y j l) =
            (y k (τ f l) : Γ(D.obj r.left, D.map r.hom ⁻¹ᵁ O k))) ∧
      ∀ j l, y j (a j l) * y j (b j l) = y j (d j l) := by
  let x' j k := Units.map (c.π.app i ⁻¹ᵁ O j).topIso.inv.hom.toMonoidHom (x j k)
  have hx' {j k} (f : j ⟶ k) l :
      (c.pt.homOfLE ((c.π.app i).preimage_mono (hO f))).appTop (x' j l) =
        (x' k (τ f l) : Γ((c.π.app i ⁻¹ᵁ O k).toScheme, ⊤)) := by
    change (c.pt.homOfLE _).appTop ((c.π.app i ⁻¹ᵁ O j).topIso.inv (x j l).val) = _
    exact (topIso_inv_restriction (X := c.pt)
      ((c.π.app i).preimage_mono (hO f)) (x j l).val).trans
        (congrArg (c.π.app i ⁻¹ᵁ O k).topIso.inv (hx f l))
  have hmul' j l : x' j (a j l) * x' j (b j l) = x' j (d j l) := by
    dsimp [x']
    rw [← map_mul, hmul]
  obtain ⟨r, z, hz, hnat, hmulz⟩ := exists_compactOpen_units D c hc i O hO hcompact
    K L x' τ hx' a b d hmul'
  let y j k := Units.map (D.map r.hom ⁻¹ᵁ O j).topIso.hom.hom.toMonoidHom (z j k)
  refine ⟨r, y, ?_, ?_, ?_⟩
  · intro j k
    apply Units.ext
    change (c.π.app r.left).appLE _ _ _
      ((D.map r.hom ⁻¹ᵁ O j).topIso.hom (z j k).val) = (x j k : Γ(c.pt, c.π.app i ⁻¹ᵁ O j))
    rw [topIso_hom_resLE]
    have he := congrArg Units.val (hz j k)
    change ((opensCone D c i (O j)).π.app r).appTop (z j k).val =
      (c.π.app i ⁻¹ᵁ O j).topIso.inv (x j k).val at he
    change (c.π.app i ⁻¹ᵁ O j).topIso.hom
      (((opensCone D c i (O j)).π.app r).appTop (z j k).val) = _
    rw [he]
    exact congrArg (fun q : Γ(c.pt, c.π.app i ⁻¹ᵁ O j) ⟶ Γ(c.pt, c.π.app i ⁻¹ᵁ O j) ↦ q (x j k))
      (c.π.app i ⁻¹ᵁ O j).topIso.inv_hom_id
  · intro j k f l
    change (D.obj r.left).presheaf.map _
      ((D.map r.hom ⁻¹ᵁ O j).topIso.hom (z j l).val) = _
    rw [topIso_hom_restriction, hnat]
    rfl
  · intro j l
    dsimp [y]
    rw [← map_mul, hmulz]

end FLT.Mazur.Approximation
