/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.TorsionPairingBilinear
public import FLT.EllipticCurve.WeilPairing
/-!
# A bilinear candidate on the geometric-torsion interface

The translation-ratio construction transports to the existing n-torsion
module. It can be passed directly to `TorsionWeilPairing.ofBilinear` once
alternation, nondegeneracy and Galois equivariance have been established.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
namespace WeierstrassCurve
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
/-- The module and additive-subgroup presentations of n-torsion are equivalent. -/
def nTorsionEquivTorsionKernel (n : ℕ) :
    E.nTorsion n ≃+ Affine.Point.torsionKernel (E⁄F) n where
  toFun P := ⟨P.val, by
    change n • P.val = 0
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property⟩
  invFun P := ⟨P.val, by
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using
      (show n • P.val = 0 from P.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The geometric construction as a bilinear map on the existing n-torsion module. -/
noncomputable def torsionPairingCandidate [IsAlgClosed F] [E.IsElliptic]
    {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0) :
    E.nTorsion n →+ E.nTorsion n →+ Additive (rootsOfUnity n F) := by
  letI : (E⁄F).IsElliptic :=
    inferInstanceAs (E.map (algebraMap F F)).IsElliptic
  let e := E.nTorsionEquivTorsionKernel n
  let b := Affine.FunctionField.torsionPairingBilinear (E⁄F) hn hchar
  exact AddMonoidHom.mk' (fun P => (b (e P)).comp e.toAddMonoidHom)
    (fun P Q => by ext R; simp)
end WeierstrassCurve
