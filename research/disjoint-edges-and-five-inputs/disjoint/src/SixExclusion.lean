import SixTerms
import KernelReplay
namespace SixTerms
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
private theorem t0 (m a b i p q) : term m a b i 0 p q = (d0 m p q && vertex (i,false) p q) := rfl
private theorem t1 (m a b i p q) : term m a b i 1 p q = (d0 m p q && vertex (i,true) p q) := rfl
private theorem t2 (m a b i p q) : term m a b i 2 p q = (d1 m a b p q && vertex (i,false) p q) := rfl
private theorem t3 (m a b i p q) : term m a b i 3 p q = (d1 m a b p q && vertex (i,true) p q) := rfl
private theorem t4 (m a b i p q) : term m a b i 4 p q = (d0 m p q && d1 m a b p q) := rfl
theorem no_terms (m : M) (a b : Bool) : passes m a b = false := by
  simp (config := {decide := true, maxSteps := 4000000}) only [passes,wins,some5,allI,all4,all3,
    mono,t0,t1,t2,t3,t4,vertex,d0,d1,lit,allowed,sep]
  kernel_bool_sat
#print axioms no_terms
end SixTerms
