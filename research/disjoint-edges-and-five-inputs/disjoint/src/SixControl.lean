import DisjointCore
namespace SixControl
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
abbrev G := edgeGraph 6 [(0,1),(2,3),(4,5),(0,3)]
def C : Circuit := ⟨[
  ⟨.or,[0,2]⟩,⟨.or,[1,3]⟩,⟨.and,[6,7]⟩,⟨.and,[4,4]⟩,
  ⟨.and,[8,0]⟩,⟨.and,[8,3]⟩,⟨.and,[9,5]⟩,⟨.or,[10,11]⟩,⟨.or,[13,12]⟩],14⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem computes : ∀ x : Fin 6 → Bool, circuitFun 6 C x = graphFun G ∅ x := by decide +kernel
theorem gates : IsAO2 6 C ∧ junk G C = {2,3} ∧ 4 ∈ centreless G C := by decide +kernel
theorem chart_violation : (0 : Fin 6) ∈ orIn 6 C (opnd C 2 0) ∧
    (2 : Fin 6) ∈ orIn 6 C (opnd C 2 0) ∧ G.Adj 0 3 ∧ G.Adj 2 3 := by decide +kernel
#print axioms computes
#print axioms gates
#print axioms chart_violation
end SixControl
