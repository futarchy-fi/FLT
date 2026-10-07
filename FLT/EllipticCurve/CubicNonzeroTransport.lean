/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionScalars
public import FLT.EllipticCurve.CubicTorsionTransport
/-! # Transport of the nonzero torsion scheme

A pointed isomorphism of full torsion schemes identifies the complements of
their zero sections. Restriction to these opens gives an actual isomorphism
over the coefficient base, in particular for admissible coordinate changes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable {V W : WeierstrassCurve R} [V.IsElliptic] [W.IsElliptic]
variable (n : ℕ) [NeZero n]

omit [NeZero n] in
/-- A torsion-group isomorphism preserves the zero section. -/
theorem torsionIso_zero (e : torsionModel V n ≅ torsionModel W n) [IsMonHom e.hom] :
    torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n :=
  congrArg Over.Hom.left (IsMonHom.one_hom e.hom)

omit [NeZero n] in
/-- The inverse of a pointed isomorphism also preserves the zero section. -/
theorem torsionIso_inv_zero (e : torsionModel V n ≅ torsionModel W n)
    (h0 : torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n) :
    torsionZeroSection W n ≫ e.inv.left = torsionZeroSection V n := by
  have hi : e.hom.left ≫ e.inv.left = 𝟙 _ := congrArg Over.Hom.left e.hom_inv_id
  calc
    _ = (torsionZeroSection V n ≫ e.hom.left) ≫ e.inv.left :=
      congrArg (fun f => f ≫ e.inv.left) h0.symm
    _ = _ := by rw [Category.assoc, hi, Category.comp_id]

/-- A pointed isomorphism maps the complement of zero into the complement of zero. -/
theorem torsionIso_mem_nonzero (e : torsionModel V n ≅ torsionModel W n)
    (h0 : torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n)
    (x : (torsionModel V n).left) (hx : x ∈ nonzeroTorsionOpen V n) :
    e.hom.left x ∈ nonzeroTorsionOpen W n := by
  intro hy
  obtain ⟨y, hy⟩ := hy
  apply hx
  refine ⟨y, ?_⟩
  have h := congrArg (fun z => e.inv.left z) hy
  have hz := congrArg (fun f : Spec (.of R) ⟶ (torsionModel V n).left => f y)
    (torsionIso_inv_zero (V := V) (W := W) n e h0)
  have hi := congrArg (fun f : torsionModel V n ⟶ torsionModel V n => f.left x) e.hom_inv_id
  exact hz.symm.trans (h.trans hi)

/-- Restriction of a pointed torsion-scheme isomorphism to the complement of zero. -/
def nonzeroTorsionTransport (e : torsionModel V n ≅ torsionModel W n)
    (h0 : torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n) :
    nonzeroTorsionModel V n ⟶ nonzeroTorsionModel W n :=
  Over.homMk
    (e.hom.left.resLE (nonzeroTorsionOpen W n) (nonzeroTorsionOpen V n)
      (torsionIso_mem_nonzero n e h0)) (by
        change (e.hom.left.resLE _ _ _) ≫
          ((nonzeroTorsionOpen W n).ι ≫ (torsionModel W n).hom) =
            (nonzeroTorsionOpen V n).ι ≫ (torsionModel V n).hom
        rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, e.hom.w])

@[reassoc (attr := simp)] theorem nonzeroTorsionTransport_inclusion
    (e : torsionModel V n ≅ torsionModel W n)
    (h0 : torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n) :
    nonzeroTorsionTransport (V := V) (W := W) n e h0 ≫ nonzeroTorsionInclusion W n =
      nonzeroTorsionInclusion V n ≫ e.hom := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι _ _

private theorem isIso_resLE_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (U : Y.Opens) (V : X.Opens) (hV : V = f ⁻¹ᵁ U) (h : V ≤ f ⁻¹ᵁ U) :
    IsIso (f.resLE U V h) := by
  subst V
  have he : f.resLE U (f ⁻¹ᵁ U) h = (f.preimageIso U).hom := by
    apply (cancel_mono U.ι).mp
    rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.preimageIso_hom_ι]
  rw [he]
  infer_instance

theorem torsionIso_preimage_nonzero (e : torsionModel V n ≅ torsionModel W n)
    (h0 : torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n) :
    nonzeroTorsionOpen V n = e.hom.left ⁻¹ᵁ nonzeroTorsionOpen W n := by
  apply le_antisymm
  · exact torsionIso_mem_nonzero (V := V) (W := W) n e h0
  · intro x hx
    have hi : e.inv.left (e.hom.left x) = x :=
      congrArg (fun f : torsionModel V n ⟶ torsionModel V n => f.left x) e.hom_inv_id
    have h := torsionIso_mem_nonzero (V := W) (W := V) n e.symm
      (torsionIso_inv_zero (V := V) (W := W) n e h0) (e.hom.left x) hx
    change e.inv.left (e.hom.left x) ∈ nonzeroTorsionOpen V n at h
    rwa [hi] at h

instance nonzeroTorsionTransportIsIso (e : torsionModel V n ≅ torsionModel W n)
    (h0 : torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n) :
    IsIso (nonzeroTorsionTransport (V := V) (W := W) n e h0) := by
  have : IsIso e.hom.left := ((Over.forget (Spec (.of R))).mapIso e).isIso_hom
  have : IsIso (nonzeroTorsionTransport (V := V) (W := W) n e h0).left :=
    isIso_resLE_of_eq e.hom.left (nonzeroTorsionOpen W n) (nonzeroTorsionOpen V n)
      (torsionIso_preimage_nonzero (V := V) (W := W) n e h0) _
  have : IsIso ((Over.forget (Spec (.of R))).map
      (nonzeroTorsionTransport (V := V) (W := W) n e h0)) :=
    ‹IsIso (nonzeroTorsionTransport (V := V) (W := W) n e h0).left›
  exact isIso_of_reflects_iso (nonzeroTorsionTransport (V := V) (W := W) n e h0)
    (Over.forget (Spec (.of R)))

/-- The nonzero torsion scheme is intrinsic under pointed torsion-scheme isomorphisms. -/
def nonzeroTorsionTransportIso (e : torsionModel V n ≅ torsionModel W n)
    (h0 : torsionZeroSection V n ≫ e.hom.left = torsionZeroSection W n) :
    nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n :=
  asIso (nonzeroTorsionTransport (V := V) (W := W) n e h0)


/-- Admissible coordinate changes identify the actual nonzero torsion parameter schemes. -/
def variableChangeNonzeroTorsionIso (W : WeierstrassCurve R) [W.IsElliptic]
    (C : VariableChange R) :
    nonzeroTorsionModel (C • W) n ≅ nonzeroTorsionModel W n :=
  nonzeroTorsionTransportIso (V := C • W) (W := W) n (variableChangeTorsionIso W C n)
    (torsionIso_zero (V := C • W) (W := W) n (variableChangeTorsionIso W C n))


end WeierstrassCurve.CubicCharts
