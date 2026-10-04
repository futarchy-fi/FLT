/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveAmpleSubgroup
public import FLT.Mazur.VeryAmplePresentationBaseChange

/-!
# Transport of relative ampleness and affine power presentations

Sheaf isomorphisms preserve the actual positive-power presentation predicate.
A global power presentation over an affine base survives arbitrary affine
base change. General locality and descent of ampleness are not assumed here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback ProjectiveSpace
variable {X S : Scheme} {f : X ⟶ S} {L M : X.Modules}

/-- Isomorphisms of actual sheaves transport relative very ample presentations. -/
theorem relativeVeryAmple_of_iso (h : RelativeVeryAmple f L) (e : M ≅ L) :
    RelativeVeryAmple f M := by
  intro U hU
  obtain ⟨p⟩ := h U hU
  exact ⟨p.ofIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso e)⟩

/-- Isomorphisms of actual sheaves preserve relative ampleness. -/
theorem RelativeAmple.of_iso (h : RelativeAmple f L) (e : M ≅ L) :
    RelativeAmple f M := by
  intro U hU
  obtain ⟨m, hm, ⟨p⟩⟩ := h U hU
  exact ⟨m, hm, ⟨p.ofIso
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (tensorPowerCongr e m))⟩⟩

/-- Relative ampleness depends on the isomorphism class of the sheaf. -/
theorem relativeAmple_iso_iff (e : L ≅ M) : RelativeAmple f L ↔ RelativeAmple f M :=
  ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

/-- A closed affine-base power presentation supplies the relative ample predicate. -/
theorem relativeAmple_of_affinePowerPresentation {A : Type} [CommRing A]
    {f : X ⟶ Spec (.of A)} [IsProper f] {m : ℕ} (hm : 0 < m)
    (p : VeryAmplePresentation f (tensorPower L m)) : RelativeAmple f L := by
  apply RelativeAmple.of_power hm
  apply relativeVeryAmple_of_iso (e := p.coefficientIso)
  exact relativeVeryAmple_pullbackOOne f (𝟙 _) p.embedding (by simpa using p.over)

/-- Any affine coefficient change preserves an actual ample power presentation. -/
theorem relativeAmple_affinePower_baseChange {A B : Type} [CommRing A] [CommRing B]
    {f : X ⟶ Spec (.of A)} [IsProper f] {m : ℕ} (hm : 0 < m)
    (p : VeryAmplePresentation f (tensorPower L m)) (φ : A →+* B) :
    RelativeAmple (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj L) :=
  relativeAmple_of_affinePowerPresentation hm
    ((p.baseChange φ).ofIso (tensorPowerIso _ L m).symm)

end FLT.Mazur.FCurve
