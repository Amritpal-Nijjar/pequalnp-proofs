import ForkTable
import KernelReplay
namespace FourFork
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
private theorem t0 (m a b e p q) : term m a b e 0 p q = (d0 m p q && vert (L e) p q) := rfl
private theorem t1 (m a b e p q) : term m a b e 1 p q = (d0 m p q && vert (R e) p q) := rfl
private theorem t2 (m a b e p q) : term m a b e 2 p q = (d1 m a b p q && vert (L e) p q) := rfl
private theorem t3 (m a b e p q) : term m a b e 3 p q = (d1 m a b p q && vert (R e) p q) := rfl
private theorem t4 (m a b e p q) : term m a b e 4 p q = (d0 m p q && d1 m a b p q) := rfl
theorem impossible (m : M) (a b : Bool) : admissible m a b=false := by
  simp (config := {decide := true, maxSteps := 4000000}) only [admissible,branchBad,needed,wins,thin,
    all5,any4,SixTerms.all4,SixTerms.some5,t0,t1,t2,t3,t4,d0,d1,lit,vert,adj,L,R]
  kernel_bool_sat
#print axioms impossible
end FourFork
