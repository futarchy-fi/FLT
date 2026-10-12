/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicOriginalIndependentCoverage
public import FLT.Mazur.IndependentCyclicModuliPullback
public import FLT.Mazur.EtaleCyclicNormalizedImageSieve

/-!
# Fppf coverage by independent cyclic charts at all positive orders

The constructed original parameters form an actual fppf family. Their image
sieve covers the original modular class and stays covering on every test scheme.
No coprimality between the cyclic order and four is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂

/-- Every original smooth etale cyclic object has an actual independent fppf presentation. -/
theorem exists_independent_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ (independentCyclicAuxiliaryScheme n).left),
      ∀ i, independentCyclicSourceModuliClass n (p i) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  have h (x : S) := exists_original_independent_neighborhood H hc ha h₂
    (V := ⊤) (x := x) (by trivial)
  choose U g hg hl hx hV p hp using h
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, p, hp⟩

/-- The independent chart's actual image covers every original class in this sector. -/
theorem independent_imageSieve_mem :
    Presheaf.imageSieve (independentCyclicModuliMap n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) ∈ Scheme.fppfTopology S := by
  obtain ⟨C, p, hp⟩ := exists_independent_fppf_cover H hc ha h₂
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨ULift.up (p i), hp i⟩

/-- Independent chart coverage persists on arbitrary, possibly nonnoetherian, tests. -/
theorem independent_pullback_imageSieve_mem {T : Scheme} (g : T ⟶ S) :
    Presheaf.imageSieve (independentCyclicModuliMap n)
      (ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) ∈
        Scheme.fppfTopology T := by
  have h := Scheme.fppfTopology.pullback_stable g (independent_imageSieve_mem H hc ha h₂)
  rwa [Presheaf.pullback_imageSieve] at h

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
