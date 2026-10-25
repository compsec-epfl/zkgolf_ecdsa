import Challenge.Instances.ECDSA_P256_Digest.Interface
import Challenge.Utils.CostR1CS

/-!
# Baseline: Longfellow's `verify_signature3`, lowered gate-for-gate to R1CS

This is *not* a challenge submission (no proofs).  It is a measuring stick: the cost of
Longfellow's own constraint structure (`lib/circuits/ecdsa/verify_circuit.h`, pinned commit)
under the challenge's score, `allocations + R1CS rows`.

Lowering conventions (all mechanical, none of them an optimisation of the *algorithm*):

* addition, subtraction and multiplication by a constant are free (linear);
* a product of two non-constant affine forms is one R1CS row; its result costs one witness
  allocation if it is later used as a multiplication operand (`mat`);
* an assertion `Σ products + affine = 0` keeps exactly one product inside its own row and
  allocates the others (`assertZeroLazy`);
* products with a constant operand fold away (Longfellow's compiler folds constants);
* shared sub-terms (powers of the selector, comparator nodes) are computed once (CSE);
* comparator nodes whose output is never used are not built (dead-code elimination).

The selector is Lean's `0..7`; Longfellow's mux polynomials are in `2v - 7`.
-/

namespace Baseline
open Challenge.Instances.ECDSA_P256_Digest.Interface

abbrev Fp := F circuitPrime
abbrev E := Expression Fp
abbrev C := Circuit Fp

def deg : E → ℕ := Challenge.CostR1CS.degree
def cst (c : Fp) : E := .const c
def sc (c : Fp) (e : E) : E := .mul (.const c) e

def constVal (e : E) : Fp := e.eval ⟨fun _ => 0, fun _ _ => #[]⟩

/-- Make `e` affine by giving every product term its own wire (1 allocation + 1 row each). -/
def mat : E → C E
  | .var v => pure (.var v)
  | .const c => pure (.const c)
  | .add a b => do
      let a' ← mat a
      let b' ← mat b
      pure (a' + b')
  | .mul a b => do
      let a' ← mat a
      let b' ← mat b
      if deg a' = 0 ∨ deg b' = 0 then pure (.mul a' b')
      else do
        let w ← Circuit.witnessField (.mul (.expr a') (.expr b'))
        Circuit.assertZero (.mul a' b' - w)
        pure w

/-- Product that is allocated immediately. -/
def mm (a b : E) : C E := mat (.mul a b)
/-- Product left pending (free until it is consumed by `mat` or an assertion). -/
def pm (a b : E) : E := .mul a b

/-- Flatten an expression into (coefficient, term) items; a term is a leaf or a product of
two non-constant factors. -/
def flat (c : Fp) : E → List (Fp × E)
  | .add a b => flat c a ++ flat c b
  | .mul a b =>
      if deg a = 0 then flat (c * constVal a) b
      else if deg b = 0 then flat (c * constVal b) a
      else [(c, .mul a b)]
  | e => [(c, e)]

def isProd : E → Bool
  | .mul _ _ => true
  | _ => false

/-- Assert `e = 0`: one product stays in the assertion's own row, the rest get wires. -/
def assertZeroLazy (e : E) : C Unit := do
  let items := flat 1 e
  let prods := items.filter (fun it => isProd it.2)
  let lins := items.filter (fun it => !isProd it.2)
  match prods with
  | [] => Circuit.assertZero e
  | (c, .mul a b) :: rest => do
      let a' ← mat a
      let b' ← mat b
      let mut acc : E := sc c (.mul a' b')
      for (c', t) in rest do
        let w ← mat t
        acc := acc + sc c' w
      for (c', t) in lins do
        acc := acc + sc c' t
      Circuit.assertZero acc
  | _ => pure ()

/-! ## Curve constants -/

def pa : Fp := Challenge.Specs.ECDSAP256.params.a
def pb : Fp := Challenge.Specs.ECDSAP256.params.b
def k3b : Fp := pb + pb + pb
def gx : Fp := Challenge.Specs.ECDSAP256.params.gx
def gy : Fp := Challenge.Specs.ECDSAP256.params.gy

/-! ## Complete addition and doubling (verify_circuit.h `addE` / `doubleE`) -/

/-- 12 products; the six that feed the outputs are left pending. -/
def addE (X1 Y1 Z1 X2 Y2 Z2 : E) : C (E × E × E) := do
  let t0 ← mm X1 X2
  let t1 ← mm Y1 Y2
  let t2 ← mm Z1 Z2
  let t3p ← mm (X1 + Y1) (X2 + Y2)
  let t3 := t3p - (t0 + t1)
  let t4p ← mm (X1 + Z1) (X2 + Z2)
  let t4 := t4p - (t0 + t2)
  let t5p ← mm (Y1 + Z1) (Y2 + Z2)
  let t5 := t5p - (t1 + t2)
  let Z3a := sc pa t4
  let X3a := sc k3b t2
  let Z3b := X3a + Z3a
  let X3b := t1 - Z3b
  let Z3c := t1 + Z3b
  let Y3p := pm X3b Z3c
  let t1' := sc 3 t0
  let t2a := sc pa t2
  let t4a := sc k3b t4
  let t1b := t1' + t2a
  let t2b := t0 - t2a
  let t2c := sc pa t2b
  let t4b := t4a + t2c
  let m1 := pm t1b t4b
  let Y3 := Y3p + m1
  let m2 := pm t5 t4b
  let X3p := pm t3 X3b
  let X3 := X3p - m2
  let m3 := pm t3 t1b
  let Z3p := pm t5 Z3c
  let Z3 := Z3p + m3
  pure (X3, Y3, Z3)

/-- 11 products; the five that feed the outputs are left pending. -/
def doubleE (X Y Z : E) : C (E × E × E) := do
  let t0 ← mm X X
  let t1 ← mm Y Y
  let t2 ← mm Z Z
  let t3 ← mm X Y
  let t3d := sc 2 t3
  let xz ← mm X Z
  let Z3d := sc 2 xz
  let X3a := sc pa Z3d
  let Y3a := sc k3b t2
  let Y3b := X3a + Y3a
  let X3b := t1 - Y3b
  let Y3c := t1 + Y3b
  let Y3p := pm X3b Y3c
  let X3p := pm t3d X3b
  let Z3e := sc k3b Z3d
  let t2a := sc pa t2
  let t3e := t0 - t2a
  let t3f := sc pa t3e
  let t3g := t3f + Z3e
  let Z3f := sc 2 t0
  let t0b := Z3f + t0
  let t0c := t0b + t2a
  let m1 := pm t0c t3g
  let Y3 := Y3p + m1
  let yz ← mm Y Z
  let t2b := sc 2 yz
  let m2 := pm t2b t3g
  let X3 := X3p - m2
  let Z3p := pm t2b t1
  let Z3 := sc 4 Z3p
  pure (X3, Y3, Z3)

/-! ## Lagrange multiplexers (bit_plucker.h `EltMuxer`), points `2i - 7` -/

def polyMulLin (p : List Fp) (r : Fp) : List Fp :=
  List.zipWith (· - ·) (0 :: p) ((p.map (· * r)) ++ [0])

/-- Monomial coefficients (low to high) of the Lagrange basis polynomials on `xs`. -/
def lagrangeBasis (xs : List Fp) : List (List Fp) :=
  (List.range xs.length).map fun i =>
    let xi := xs.getD i 0
    let others := ((List.range xs.length).filter (fun j => j != i)).map (fun j => xs.getD j 0)
    let num := others.foldl polyMulLin [1]
    let den := others.foldl (fun acc xj => acc * (xi - xj)) 1
    num.map (· * den⁻¹)

def pts8 : List Fp := (List.range 8).map fun i => (2 * (i : Fp) - 7)
def pts9 : List Fp := pts8 ++ [9]
def basis8 : List (List Fp) := lagrangeBasis pts8
def basis9 : List (List Fp) := lagrangeBasis pts9

/-- Coefficient expressions `coeff_j = Σ_i basis_i[j] * arr_i`. -/
def muxCoeffs (basis : List (List Fp)) (arr : List E) : List E :=
  (List.range basis.length).map fun j =>
    (List.range arr.length).foldl
      (fun acc i => acc + sc ((basis.getD i []).getD j 0) (arr.getD i (cst 0))) (cst 0)

/-- `Σ_j coeff_j * x^j` (pending products). -/
def muxEval (coeffs xi : List E) : E :=
  (List.range coeffs.length).foldl
    (fun acc j => acc + .mul (coeffs.getD j (cst 0)) (xi.getD j (cst 0))) (cst 0)

/-! ## Bitwise `a < n` against the constant order (logic.h `lt_reduce`) -/

/-- Returns `(eq, lt)` for bits `[i0,i1)`; `none` for `lt` means constant 0 and for `eq`
means "not built because unused". -/
def ltReduce (nb : Nat → Bool) (a : Nat → E) :
    Nat → Nat → Nat → Bool → C (Option E × Option E)
  | 0, _, _, _ => pure (none, none)
  | fuel + 1, i0, i1, needEq =>
    if i1 - i0 > 1 then do
      let im := i0 + (i1 - i0) / 2
      let (eq0, lt0) ← ltReduce nb a fuel i0 im needEq
      let (eq1, lt1) ← ltReduce nb a fuel im i1 (needEq || lt0.isSome)
      let xeq ← match needEq, eq1, eq0 with
        | true, some e1, some e0 => do pure (some (← mm e1 e0))
        | _, _, _ => pure none
      let xlt ← match lt0, eq1 with
        | some l0, some e1 => do
            let l0' ← mat l0
            let p := pm e1 l0'
            pure (some (match lt1 with | none => p | some l1 => l1 + p))
        | _, _ => pure lt1
      pure (xeq, xlt)
    else
      let ai := a i0
      let eq := if needEq then some (if nb i0 then ai else cst 1 - ai) else none
      let lt := if nb i0 then some (cst 1 - ai) else none
      pure (eq, lt)

/-! ## The circuit -/

def isOnCurve (x y : E) : C Unit := do
  let xx ← mm x x
  assertZeroLazy (.mul y y - (.mul x xx + sc pa x + cst pb))

def pointEquality (x y z px py : E) : C Unit := do
  let z' ← mat z
  assertZeroLazy (x - .mul z' px)
  assertZeroLazy (y - .mul z' py)

def orderBit (j : Nat) : Bool := Challenge.Specs.ECDSAP256.n.testBit j

def main (inp : Var Input Fp) : C Unit := do
  let one := cst 1
  let zero := cst 0
  let pre := inp.pre.toList
  let pk := fun i => pre.getD i zero
  -- table checks
  let (a1x, a1y, a1z) ← addE (cst gx) (cst gy) one inp.pkX inp.pkY one
  let (a2x, a2y, a2z) ← addE inp.rx inp.ry one (cst gx) (cst gy) one
  let (a3x, a3y, a3z) ← addE inp.rx inp.ry one inp.pkX inp.pkY one
  let (a4x, a4y, a4z) ← addE (cst gx) (cst gy) one (pk 4) (pk 5) one
  pointEquality a1x a1y a1z (pk 0) (pk 1)
  pointEquality a2x a2y a2z (pk 2) (pk 3)
  pointEquality a3x a3y a3z (pk 4) (pk 5)
  pointEquality a4x a4y a4z (pk 6) (pk 7)
  -- multiplexer coefficients
  let arrX := [zero, cst gx, inp.pkX, pk 0, inp.rx, pk 2, pk 4, pk 6]
  let arrY := [one, cst gy, inp.pkY, pk 1, inp.ry, pk 3, pk 5, pk 7]
  let cX := muxCoeffs basis8 arrX
  let cY := muxCoeffs basis8 arrY
  let cZ := muxCoeffs basis8 [zero, one, one, one, one, one, one, one]
  let cE := muxCoeffs basis8 [zero, one, zero, one, zero, one, zero, one]
  let cR := muxCoeffs basis8 [zero, zero, one, one, zero, zero, one, one]
  let cS := muxCoeffs basis8 [zero, zero, zero, zero, one, one, one, one]
  let cV := muxCoeffs basis9 [zero, zero, zero, zero, zero, zero, zero, zero, one]
  let bis := inp.bi.toList
  let ix := inp.intX.toList
  let iy := inp.intY.toList
  let iz := inp.intZ.toList
  let mut ax := zero
  let mut ay := one
  let mut az := zero
  let mut est := zero
  let mut rst := zero
  let mut sst := zero
  let mut rbits : Array E := #[]
  let mut sbits : Array E := #[]
  for i in [0:256] do
    let bp := sc 2 (bis.getD i zero) - cst 7
    -- powers of the selector: x^0 .. x^8
    let mut xi : Array E := #[one, bp]
    for k in [2:9] do
      let w ← mm (xi.getD (k - k / 2) zero) (xi.getD (k / 2) zero)
      xi := xi.push w
    let xl := xi.toList
    let tx ← mat (muxEval cX xl)
    let ty ← mat (muxEval cY xl)
    let tz := muxEval cZ xl
    let ebi := muxEval cE xl
    let rbi := muxEval cR xl
    let sbi := muxEval cS xl
    est := ebi + sc 2 est
    rst := rbi + sc 2 rst
    sst := sbi + sc 2 sst
    rbits := rbits.push rbi
    sbits := sbits.push sbi
    Circuit.assertZero (muxEval cV xl)
    if i > 0 then
      let (dx, dy, dz) ← doubleE ax ay az
      ax ← mat dx
      ay ← mat dy
      az ← mat dz
    let (nx, ny, nz) ← addE ax ay az tx ty tz
    if i < 255 then
      assertZeroLazy (nx - ix.getD i zero)
      assertZeroLazy (ny - iy.getD i zero)
      assertZeroLazy (nz - iz.getD i zero)
      ax := ix.getD i zero
      ay := iy.getD i zero
      az := iz.getD i zero
    else
      assertZeroLazy nx
      assertZeroLazy nz
  assertZeroLazy (est - inp.digest)
  assertZeroLazy (rst - inp.rx)
  isOnCurve inp.pkX inp.pkY
  isOnCurve inp.rx inp.ry
  assertZeroLazy (.mul inp.rx inp.rxInv - one)
  assertZeroLazy (.mul sst inp.sInv - one)
  assertZeroLazy (.mul inp.pkX inp.pkInv - one)
  let rb := fun j => rbits.getD (255 - j) zero
  let sb := fun j => sbits.getD (255 - j) zero
  let (_, ltR) ← ltReduce orderBit rb 9 0 256 false
  let (_, ltS) ← ltReduce orderBit sb 9 0 256 false
  assertZeroLazy (ltR.getD zero - one)
  assertZeroLazy (ltS.getD zero - one)

end Baseline
