/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RetainedSubringGrading
public import FLT.Mazur.HomogeneousLocalizationRegradedMap

/-!
# Retaining degrees preserves homogeneous affine charts

For a homogeneous element in a retained degree, inclusion of the retained
subring induces an isomorphism on degree-zero localizations. Every numerator
of a full-ring fraction already has a retained degree.
-/

@[expose] public noncomputable section

open HomogeneousLocalization

namespace FLT.Mazur.RetainedSubringLocalization

open RetainedSubringGrading

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (q : ℕ) [GradedRing (grade 𝒜 q)]
  (f : ring 𝒜 q)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (grade 𝒜 q)] in
/-- Inclusion of the retained ring maps the powers of the original denominator to its powers. -/
theorem powers_le : Submonoid.powers f ≤
    (Submonoid.powers (f : A)).comap (ring 𝒜 q).subtype := by
  rintro _ ⟨k, rfl⟩
  exact ⟨k, (map_pow (ring 𝒜 q).subtype f k).symm⟩

/-- The chart map applies the original subring inclusion to numerator and denominator. -/
def inclusion : Away (grade 𝒜 q) f →+* Away 𝒜 (f : A) :=
  HomogeneousLocalizationRegradedMap.map (grade 𝒜 q) 𝒜 (ring 𝒜 q).subtype
    (q * ·) (fun _ _ ha ↦ ha) (powers_le 𝒜 q f)

/-- On ordinary fractions the chart map is the actual localization of subring inclusion. -/
theorem inclusion_val (z : Away (grade 𝒜 q) f) :
    (inclusion 𝒜 q f z).val =
      IsLocalization.map (Localization.Away (f : A)) (ring 𝒜 q).subtype
        (powers_le 𝒜 q f) z.val :=
  HomogeneousLocalizationRegradedMap.map_val _ _ _ _ _ _ z

/-- Retaining degrees introduces no new equality between homogeneous fractions. -/
theorem inclusion_injective : Function.Injective (inclusion 𝒜 q f) := by
  let _ : IsLocalization ((Submonoid.powers f).map (ring 𝒜 q).subtype)
      (Localization.Away (f : A)) := by
    rw [Submonoid.map_powers]
    change IsLocalization (Submonoid.powers (f : A)) (Localization.Away (f : A))
    infer_instance
  have hi := IsLocalization.map_injective_of_injective (Submonoid.powers f)
    (Localization.Away f) (Localization.Away (f : A))
    (g := (ring 𝒜 q).subtype) Subtype.val_injective
  intro x y he
  apply val_injective
  apply hi
  exact (inclusion_val 𝒜 q f x).symm.trans
    ((congrArg HomogeneousLocalization.val he).trans (inclusion_val 𝒜 q f y))

/-- A retained homogeneous denominator keeps every numerator of a degree-zero fraction. -/
theorem inclusion_surjective {d : ℕ} (hf : f ∈ grade 𝒜 q d) :
    Function.Surjective (inclusion 𝒜 q f) := by
  intro z
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
  have ha' : a ∈ 𝒜 (q * (k • d)) := by
    simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_left_comm] using ha
  let b : ring 𝒜 q := ⟨a, Subring.subset_closure (Set.mem_iUnion.mpr ⟨k • d, ha'⟩)⟩
  refine ⟨Away.mk (grade 𝒜 q) hf k b ha', ?_⟩
  apply val_injective
  rw [inclusion_val, Away.val_mk, Away.val_mk]
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

/-- The retained and full section charts have their original fraction-ring isomorphism. -/
def ringEquiv {d : ℕ} (hf : f ∈ grade 𝒜 q d) :
    Away (grade 𝒜 q) f ≃+* Away 𝒜 (f : A) :=
  RingEquiv.ofBijective (inclusion 𝒜 q f)
    ⟨inclusion_injective 𝒜 q f, inclusion_surjective 𝒜 q f hf⟩

/-- The isomorphism retains the original chart map. -/
theorem ringEquiv_apply {d : ℕ} (hf : f ∈ grade 𝒜 q d)
    (z : Away (grade 𝒜 q) f) : ringEquiv 𝒜 q f hf z = inclusion 𝒜 q f z := rfl

end FLT.Mazur.RetainedSubringLocalization
