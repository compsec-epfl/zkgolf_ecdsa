import Baseline.Optimized

/-! Experimental projected-signature circuit. NOT a submission for the current
pointwise-witness challenge. Five fixed inputs; all auxiliary data is allocated. -/
namespace Baseline.Projected.Offset
open Baseline

structure Input (F : Type) where
  pkX : F
  pkY : F
  digest : F
  r : F
  s : F
  deriving ProvableStruct

abbrev Pt := E × E

def hint (i : Nat) : C E :=
  Circuit.witnessField (.hintGet "offset" 1 (.const i.toUInt64) ⟨0, by decide⟩)

def nonzero (x : E) : C E := do
  let inv ← Circuit.witnessField (.inv (.expr x))
  Circuit.assertZero (pm x inv - cst 1)
  pure inv

def affAdd (p q : Pt) : C Pt := do
  let inv ← nonzero (q.1 - p.1)
  let l ← Circuit.witnessField (.mul (.expr (q.2-p.2)) (.expr inv))
  Circuit.assertZero (pm (q.1-p.1) l - (q.2-p.2))
  let x ← Circuit.witnessField (.add (.mul (.expr l) (.expr l)) (.expr (-p.1-q.1)))
  Circuit.assertZero (pm l l - p.1 - q.1 - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l) (.expr (p.1-x))) (.expr (-p.2)))
  Circuit.assertZero (pm l (p.1-x) - p.2 - y)
  pure (x,y)

def affDouble (p : Pt) : C Pt := do
  let xx ← mm p.1 p.1
  -- The slope row and nonsingularity imply 2*y != 0 (Algebra.double_denominator_ne).
  let l ← Circuit.witnessField (.mul (.expr (sc 3 xx + cst pa)) (.inv (.expr (sc 2 p.2))))
  Circuit.assertZero (pm (sc 2 p.2) l - sc 3 xx - cst pa)
  let x ← Circuit.witnessField (.add (.mul (.expr l) (.expr l)) (.expr (-sc 2 p.1)))
  Circuit.assertZero (pm l l - sc 2 p.1 - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l) (.expr (p.1-x))) (.expr (-p.2)))
  Circuit.assertZero (pm l (p.1-x) - p.2 - y)
  pure (x,y)

/-- ELM prefix. The first denominator is guarded; the second is implied by
the curve equations and the first three rows (Algebra.elm_second_denominator_ne). -/
def elmCore (p q : Pt) : C Pt := do
  let inv1 ← nonzero (q.1-p.1)
  let l1 ← Circuit.witnessField (.mul (.expr (q.2-p.2)) (.expr inv1))
  Circuit.assertZero (pm (q.1-p.1) l1 - (q.2-p.2))
  let xu ← Circuit.witnessField (.add (.mul (.expr l1) (.expr l1)) (.expr (-p.1-q.1)))
  Circuit.assertZero (pm l1 l1 - p.1 - q.1 - xu)
  let l2 ← Circuit.witnessField (.add (.mul (.expr (sc 2 p.2)) (.inv (.expr (p.1-xu)))) (.expr (-l1)))
  Circuit.assertZero (pm (l1+l2) (p.1-xu) - sc 2 p.2)
  pure (xu,l2)

/-- 2P+Q with the intermediate y coordinate omitted. -/
def elm (p q : Pt) : C Pt := do
  let (xu,l2) ← elmCore p q
  let x ← Circuit.witnessField (.add (.mul (.expr l2) (.expr l2)) (.expr (-p.1-xu)))
  Circuit.assertZero (pm l2 l2 - p.1 - xu - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l2) (.expr (p.1-x))) (.expr (-p.2)))
  Circuit.assertZero (pm l2 (p.1-x) - p.2 - y)
  pure (x,y)

/-- Final step uses its known target directly: no redundant output wires. -/
def elmTo (p q target : Pt) : C Unit := do
  let (xu,l2) ← elmCore p q
  Circuit.assertZero (pm l2 l2 - p.1 - xu - target.1)
  Circuit.assertZero (pm l2 (p.1-target.1) - p.2 - target.2)

abbrev KP := ProjectivePoint Fp

def affine (p : KP) : Fp × Fp := (p.X * p.Z⁻¹, p.Y * p.Z⁻¹)
def gPoint : KP := { X := gx, Y := gy, Z := 1 }
def mulG (k : Nat) : KP :=
  bsmul (padBits (natToBits (k % Challenge.Specs.ECDSAP256.n)) 256)
    gPoint Challenge.Specs.ECDSAP256.params

/-- Constants only: [(4+d)4^i G] for d=0..3; none is infinity. -/
def fixedTables : Array (Array (Fp × Fp)) :=
  (List.range 128).toArray.map fun i =>
    (List.range 4).toArray.map fun d => affine (mulG ((4+d)*4^i))

def fixedShift : Fp × Fp := affine (mulG (4 * ((4^128 - 1)/3)))

/-- Constant four-way point mux; one shared bit product for both coordinates. -/
def muxConst4 (b0 b1 : E) (tab : Array (Fp × Fp)) : C Pt := do
  let b01 ← mm b0 b1
  let coord (get : Fp × Fp → Fp) :=
    let v0 := get (tab.getD 0 (0,0))
    let v1 := get (tab.getD 1 (0,0))
    let v2 := get (tab.getD 2 (0,0))
    let v3 := get (tab.getD 3 (0,0))
    cst v0 + sc (v1-v0) b0 + sc (v2-v0) b1 + sc (v3-v2-v1+v0) b01
  pure (coord Prod.fst, coord Prod.snd)

def mux4 (b0 b1 : E) (p0 p1 p2 p3 : Pt) : C Pt := do
  let coord (get : Pt → E) : C E := do
    let a ← Optimized.sel b0 (get p0) (get p1)
    let b ← Optimized.sel b0 (get p2) (get p3)
    Optimized.sel b1 a b
  return (← coord Prod.fst, ← coord Prod.snd)

/-- The precomputed original Longfellow table remains constrained exactly as before. -/
def originalTable (q r : Pt) : C (Array Pt) := do
  let mut pre : Array E := #[]
  for i in [0:8] do pre := pre.push (← hint (3+i))
  let get := fun k => pre.getD k (cst 0)
  let pairs := #[(cst gx,cst gy,q.1,q.2,0),
    (r.1,r.2,cst gx,cst gy,2), (r.1,r.2,q.1,q.2,4),
    (cst gx,cst gy,get 4,get 5,6)]
  for (ax,ay,bx,byy,j) in pairs do
    let (x,y,z) ← Baseline.addE ax ay (cst 1) bx byy (cst 1)
    pointEquality x y z (get j) (get (j+1))
  return #[(get 0,get 1),(get 2,get 3),(get 4,get 5),(get 6,get 7)]

def main (inp : Var Input Fp) : C Unit := do
  let ry ← hint 0
  let hx ← hint 1
  let hy ← hint 2
  let q := (inp.pkX,inp.pkY)
  let r := (inp.r,ry)
  let h := (hx,hy)
  isOnCurve q.1 q.2
  isOnCurve r.1 r.2
  isOnCurve hx hy
  let _ ← nonzero inp.pkX
  let _ ← nonzero inp.r
  let negS := cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s
  let _ ← nonzero negS
  let pre ← originalTable q r
  let qr := pre.getD 2 (cst 0,cst 0)
  let mut eb : Array E := #[]
  let mut rb : Array E := #[]
  let mut sb : Array E := #[]
  let mut ee := cst 0
  let mut rr := cst 0
  let mut ss := cst 0
  for i in [0:256] do
    let be ← hint (11+3*i)
    let br ← hint (12+3*i)
    let bs ← hint (13+3*i)
    Optimized.assertBool be
    Optimized.assertBool br
    Optimized.assertBool bs
    eb := eb.push be
    rb := rb.push br
    sb := sb.push bs
    ee := ee + sc ((2 : Fp)^i) be
    rr := rr + sc ((2 : Fp)^i) br
    ss := ss + sc ((2 : Fp)^i) bs
  Circuit.assertZero (ee-inp.digest)
  Circuit.assertZero (rr-inp.r)
  Circuit.assertZero (ss-negS)
  Optimized.assertLtOrder (fun i => rb.getD i (cst 0))
  Optimized.assertLtOrder (fun i => sb.getD i (cst 0))
  -- E = H + eG, with a nonzero constant offset in every fixed-base window.
  let shift := fixedShift
  let mut ep ← affAdd h (cst shift.1,cst (-shift.2))
  let tables := fixedTables
  for i in [0:128] do
    let t ← muxConst4 (eb.getD (2*i) (cst 0)) (eb.getD (2*i+1) (cst 0))
      (tables.getD i #[])
    ep ← affAdd ep t
  -- Alternating offsets allow both ELM denominators to be avoided by choosing H.
  let hh ← affDouble h
  let hhh ← affAdd hh h
  let mut plus : Array Pt := #[hhh]
  let nhhh := (hhh.1,-hhh.2)
  let mut minus : Array Pt := #[nhhh]
  for t in #[q,r,qr] do
    plus := plus.push (← affAdd hhh t)
    minus := minus.push (← affAdd nhhh t)
  let mut acc := (hx,-hy)
  for j in [0:256] do
    let i := 255-j
    let tab := if j%2 == 0 then plus else minus
    let t ← mux4 (rb.getD i (cst 0)) (sb.getD i (cst 0))
      (tab.getD 0 h) (tab.getD 1 h) (tab.getD 2 h) (tab.getD 3 h)
    if j == 255 then
      elmTo acc t (ep.1,-ep.2)
    else
      acc ← elm acc t

end Baseline.Projected.Offset
