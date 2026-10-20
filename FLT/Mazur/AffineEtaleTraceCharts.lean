/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleTraceSurjectivity
public import FLT.Mazur.AffineOpenNorm

/-!
# Trace units on full finite free open preimages

The original geometric section restricts through the cartesian square. Hence
every finite free open preimage has a trace-one section in its actual ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleTraceCharts
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Y ⟶ X) (hr : r ≫ f = 𝟙 Y)

/-- The original section restricted to an entire open preimage. -/
def restrictedSection (V : Y.Opens) : V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  ((isPullback_morphismRestrict f V).flip).lift (V.ι ≫ r) (𝟙 _)
    (by simp only [Category.assoc, hr, Category.comp_id, Category.id_comp])

/-- The restricted section retracts the actual restricted morphism. -/
theorem section_comp (V : Y.Opens) : restrictedSection f r hr V ≫ (f ∣_ V) = 𝟙 _ := by
  apply IsPullback.lift_snd

variable [IsAffineHom f] [Etale f]

include hr in
/-- A finite free chart carries a trace-one element for all original arrows above it. -/
theorem exists_trace_one (V : Y.affineOpens) (hV : AffineOpenNorm.HasBasis f V) :
    ∃ s : Γ((f ⁻¹ᵁ V.1).toScheme, ⊤),
      AffineCartesianTrace.sectionTrace (f ∣_ V.1) s = 1 := by
  let _ : IsAffine V.1.toScheme := V.2
  let _ : IsAffine (f ⁻¹ᵁ V.1).toScheme := V.2.preimage f
  let _ : Etale (f ∣_ V.1) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f V.1).flip (inferInstanceAs (Etale f))
  let _ := (f ∣_ V.1).appTop.hom.toAlgebra
  obtain ⟨n, ⟨b⟩⟩ := hV
  exact AffineEtaleTraceSurjectivity.sectionTrace_surjective (f ∣_ V.1)
    (restrictedSection f r hr V.1) (section_comp f r hr V.1) b 1

end FLT.Mazur.AffineEtaleTraceCharts
