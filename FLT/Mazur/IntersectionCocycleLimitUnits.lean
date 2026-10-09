/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompactOpenAmbientUnitDescent
public import FLT.Mazur.IntersectionUnitCocycleRecovery

/-!
# Actual transition units descend through scheme limits

Start with a cocycle on the inverse-image charts of a fixed finite atlas.
Its genuine units, restriction laws and triple equations descend together
to one refinement, without a presentation hypothesis on the original scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Descend the prescribed cocycle's units on all intersections at one stage. -/
theorem exists_intersectionCocycle_limit_units {ι : Type u} [Finite ι]
    (i : I) (U : ι → (D.obj i).Opens)
    (hcompact : ∀ s, IsCompact (finiteIntersectionOpen U s : Set (D.obj i)))
    (g : Cocycle (fun j ↦ c.π.app i ⁻¹ᵁ U j)) :
    ∃ (r : Over i)
      (y : ∀ s, IntersectionPair s → Γ(D.obj r.left, D.map r.hom ⁻¹ᵁ
        finiteIntersectionOpen U s)ˣ),
      (∀ s k, Units.map ((c.π.app r.left).appLE _ _
        (by rw [← Scheme.Hom.comp_preimage, c.w])).hom.toMonoidHom (y s k) =
          g.unit k.1.val k.2.val (c.π.app i ⁻¹ᵁ finiteIntersectionOpen U s)
            ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.1))
            ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.2))) ∧
      (∀ {s t} (h : s ≤ t) k, res ((D.map r.hom).preimage_mono
          (finiteIntersectionOpen_antitone U h)) (y s k : Γ(D.obj r.left, _)) =
            (y t (intersectionPairMap (homOfLE h) k) : Γ(D.obj r.left, _))) ∧
      ∀ s (k : IntersectionTriple s),
        y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2) := by
  let O := finiteIntersectionOpen U
  let x (s : NonemptyChartSet ι) (k : IntersectionPair s) :
      Γ(c.pt, c.π.app i ⁻¹ᵁ O s)ˣ :=
    g.unit k.1.val k.2.val _
      ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.1))
      ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.2))
  have hx {s t : NonemptyChartSet ι} (f : s ⟶ t) (k : IntersectionPair s) :
      c.pt.presheaf.map (homOfLE ((c.π.app i).preimage_mono
        (finiteIntersectionOpen_antitone U (leOfHom f)))).op (x s k) =
          (x t (intersectionPairMap f k) : Γ(c.pt, _)) :=
    g.natural _ _ _ _ _
  have hmul (s : NonemptyChartSet ι) (k : IntersectionTriple s) :
      x s (k.1, k.2.1) * x s (k.2.1, k.2.2) = x s (k.1, k.2.2) :=
    g.cocycle _ _ _ _ _ _ _
  obtain ⟨r, y, hy, hnat, hmul'⟩ := exists_compactOpen_ambient_units D c hc i O
    (fun f ↦ finiteIntersectionOpen_antitone U (leOfHom f)) hcompact
    IntersectionPair IntersectionTriple x (fun f ↦ intersectionPairMap f) hx
    (fun _ k ↦ (k.1, k.2.1)) (fun _ k ↦ (k.2.1, k.2.2))
    (fun _ k ↦ (k.1, k.2.2)) hmul
  exact ⟨r, y, hy, fun h k ↦ hnat (homOfLE h) k, hmul'⟩

end FLT.Mazur.Approximation
