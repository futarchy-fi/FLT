/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjLineRatioCocycle

/-!
# Structure-sheaf transition cocycles on Proj

Homogeneous ratios define units on the actual chart intersections, with
restriction and cocycle identities.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.GradedProjLine

variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type u} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- A homogeneous transition as a unit of the actual overlap sections. -/
def transitionSection (n : ℤ) (i j : ι) :
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 (f i * f j))ˣ :=
  Units.map (Proj.awayToSection 𝒜 (f i * f j)).hom.toMonoidHom
    (transitionUnit 𝒜 f hf n i j)

/-- Restriction of units in the structure sheaf. -/
def restrictUnits {U V : (Proj 𝒜).Opens} (h : V ≤ U) :
    Γ(Proj 𝒜, U)ˣ →* Γ(Proj 𝒜, V)ˣ :=
  Units.map ((Proj 𝒜).presheaf.map (homOfLE h).op).hom.toMonoidHom

/-- Unit restriction respects composition of open inclusions. -/
lemma restrictUnits_comp {U V W : (Proj 𝒜).Opens} (h : V ≤ U) (h' : W ≤ V)
    (s : Γ(Proj 𝒜, U)ˣ) :
    restrictUnits 𝒜 h' (restrictUnits 𝒜 h s) = restrictUnits 𝒜 (h'.trans h) s := by
  apply Units.ext
  exact congrArg (fun f ↦ f.hom (s : Γ(Proj 𝒜, U)))
    ((Proj 𝒜).presheaf.map_comp (homOfLE h).op (homOfLE h').op).symm

/-- The homogeneous localization comparison also compares units. -/
lemma awayUnit_restrict {f g x : A} {d : ℕ}
    (hg : g ∈ 𝒜 d) (hx : x = f * g) (s : (Away 𝒜 f)ˣ) :
    restrictUnits 𝒜 (Proj.basicOpen_mono _ _ _ ⟨g, hx⟩)
        (Units.map (Proj.awayToSection 𝒜 f).hom.toMonoidHom s) =
      Units.map (Proj.awayToSection 𝒜 x).hom.toMonoidHom
        (Units.map (awayMap 𝒜 hg hx).toMonoidHom s) := by
  apply Units.ext
  exact congrArg (fun φ ↦ φ.hom (s : Away 𝒜 f))
    (Proj.awayMap_awayToSection 𝒜 hg hx).symm

/-- The actual intersection of three standard opens. -/
abbrev tripleOpen (i j k : ι) : (Proj 𝒜).Opens :=
  chart 𝒜 f i ⊓ chart 𝒜 f j ⊓ chart 𝒜 f k

lemma tripleOpen_eq (i j k : ι) :
    tripleOpen 𝒜 f i j k = Proj.basicOpen 𝒜 (f i * f j * f k) := by
  simp only [tripleOpen, chart, Proj.basicOpen_mul]

lemma tripleOpen_le₁₂ (i j k : ι) :
    tripleOpen 𝒜 f i j k ≤ Proj.basicOpen 𝒜 (f i * f j) := by
  rw [Proj.basicOpen_mul]
  exact inf_le_left

lemma tripleOpen_le₂₃ (i j k : ι) :
    tripleOpen 𝒜 f i j k ≤ Proj.basicOpen 𝒜 (f j * f k) := by
  rw [Proj.basicOpen_mul]
  exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

lemma tripleOpen_le₁₃ (i j k : ι) :
    tripleOpen 𝒜 f i j k ≤ Proj.basicOpen 𝒜 (f i * f k) := by
  rw [Proj.basicOpen_mul]
  exact le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- Map triple-overlap coordinates to sections on the actual intersection. -/
def tripleUnitsToSection (i j k : ι) :
    (tripleRing 𝒜 f i j k)ˣ →* Γ(Proj 𝒜, tripleOpen 𝒜 f i j k)ˣ :=
  (restrictUnits 𝒜 (tripleOpen_eq 𝒜 f i j k).le).comp
    (Units.map (Proj.awayToSection 𝒜 (f i * f j * f k)).hom.toMonoidHom)

lemma transitionSection_restrict₁₂ (n : ℤ) (i j k : ι) :
    restrictUnits 𝒜 (tripleOpen_le₁₂ 𝒜 f i j k) (transitionSection 𝒜 f hf n i j) =
      tripleUnitsToSection 𝒜 f i j k
        (Units.map (toTriple₁₂ 𝒜 f hf i j k).toMonoidHom (transitionUnit 𝒜 f hf n i j)) := by
  rw [tripleUnitsToSection, MonoidHom.comp_apply, toTriple₁₂, ← awayUnit_restrict]
  exact (restrictUnits_comp 𝒜 _ _ _).symm

lemma transitionSection_restrict₂₃ (n : ℤ) (i j k : ι) :
    restrictUnits 𝒜 (tripleOpen_le₂₃ 𝒜 f i j k) (transitionSection 𝒜 f hf n j k) =
      tripleUnitsToSection 𝒜 f i j k
        (Units.map (toTriple₂₃ 𝒜 f hf i j k).toMonoidHom (transitionUnit 𝒜 f hf n j k)) := by
  rw [tripleUnitsToSection, MonoidHom.comp_apply, toTriple₂₃, ← awayUnit_restrict]
  exact (restrictUnits_comp 𝒜 _ _ _).symm

lemma transitionSection_restrict₁₃ (n : ℤ) (i j k : ι) :
    restrictUnits 𝒜 (tripleOpen_le₁₃ 𝒜 f i j k) (transitionSection 𝒜 f hf n i k) =
      tripleUnitsToSection 𝒜 f i j k
        (Units.map (toTriple₁₃ 𝒜 f hf i j k).toMonoidHom (transitionUnit 𝒜 f hf n i k)) := by
  rw [tripleUnitsToSection, MonoidHom.comp_apply, toTriple₁₃, ← awayUnit_restrict]
  exact (restrictUnits_comp 𝒜 _ _ _).symm

/-- The twisting transitions satisfy the structure-sheaf cocycle on triple intersections. -/
lemma transitionSection_cocycle (n : ℤ) (i j k : ι) :
    restrictUnits 𝒜 (tripleOpen_le₁₂ 𝒜 f i j k) (transitionSection 𝒜 f hf n i j) *
      restrictUnits 𝒜 (tripleOpen_le₂₃ 𝒜 f i j k) (transitionSection 𝒜 f hf n j k) =
    restrictUnits 𝒜 (tripleOpen_le₁₃ 𝒜 f i j k) (transitionSection 𝒜 f hf n i k) := by
  rw [transitionSection_restrict₁₂, transitionSection_restrict₂₃,
    transitionSection_restrict₁₃, ← map_mul, transitionUnit_cocycle]

@[simp] lemma transitionSection_self (n : ℤ) (i : ι) :
    transitionSection 𝒜 f hf n i i = 1 := by
  simp only [transitionSection, transitionUnit, ratioUnit_self, one_zpow, map_one]

/-- The transition unit, with its domain written as an intersection of charts. -/
def twistTransition (n : ℤ) (i j : ι) :
    Γ(Proj 𝒜, chart 𝒜 f i ⊓ chart 𝒜 f j)ˣ :=
  restrictUnits 𝒜 (Proj.basicOpen_mul 𝒜 (f i) (f j)).ge (transitionSection 𝒜 f hf n i j)

@[simp]
lemma twistTransition_self (n : ℤ) (i : ι) : twistTransition 𝒜 f hf n i i = 1 := by
  simp only [twistTransition, transitionSection_self, map_one]

@[simp]
lemma twistTransition_zero (i j : ι) : twistTransition 𝒜 f hf 0 i j = 1 := by
  simp only [twistTransition, transitionSection, transitionUnit, zpow_zero, map_one]

/-- The unit cocycle in intersection notation, ready for module descent. -/
lemma twistTransition_cocycle (n : ℤ) (i j k : ι) :
    restrictUnits 𝒜 (inf_le_left : tripleOpen 𝒜 f i j k ≤ _)
        (twistTransition 𝒜 f hf n i j) *
      restrictUnits 𝒜 (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        tripleOpen 𝒜 f i j k ≤ _) (twistTransition 𝒜 f hf n j k) =
    restrictUnits 𝒜 (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      tripleOpen 𝒜 f i j k ≤ _) (twistTransition 𝒜 f hf n i k) := by
  dsimp only [twistTransition, tripleOpen, chart]
  rw [restrictUnits_comp, restrictUnits_comp, restrictUnits_comp]
  exact transitionSection_cocycle 𝒜 f hf n i j k

end FLT.Mazur.GradedProjLine
