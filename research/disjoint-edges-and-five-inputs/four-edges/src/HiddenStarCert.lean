import KernelReplay
namespace HiddenStarCert
abbrev V := Fin 6
abbrev M := Fin 4 → V → Bool
def good (x : V→Bool) := !((x 0 || x 3) && (x 1 || x 2 || x 4 || x 5)) && !(x 1 && x 2) && !(x 4 && x 5)
def equal (x y : V→Bool) := (x 0 == y 0) && (x 1 == y 1) && (x 2 == y 2) &&
  (x 3 == y 3) && (x 4 == y 4) && (x 5 == y 5)
def compatible (x y : V→Bool) := good x || good y || equal x y
def raw (m : M) := compatible (m 0) (m 1) && compatible (m 0) (m 2) && compatible (m 0) (m 3) &&
  compatible (m 1) (m 2) && compatible (m 1) (m 3) && compatible (m 2) (m 3)
def lit (x : V→Bool) (p q : V) := x p || x q
def signal (m : M) (a b r s : Bool) (p q : V) :=
  let d := lit (m 0) p q && lit (m 1) p q
  (r && d) || (s && ((lit (m 2) p q || (a && d)) && (lit (m 3) p q || (b && d))))
def tests (y : V→V→Bool) := y 0 1 && y 0 2 && y 3 4 && y 3 5 &&
  !y 0 0 && !y 3 3 && !y 0 3 && !y 0 4 && !y 0 5 && !y 3 1 && !y 3 2
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
/-- Two dirty gates and at most one distinct bad raw mask cannot make the
    single visible signal pass the four positive and seven guarded negative rows. -/
theorem impossible (m : M) (a b r s : Bool) : (raw m && tests (signal m a b r s))=false := by
  simp only [raw,compatible,good,equal,tests,signal,lit]
  kernel_bool_sat
#print axioms impossible
end HiddenStarCert
